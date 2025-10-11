package main

import (
	"context"
	"crypto/aes"
	"crypto/cipher"
	"crypto/rand"
	"encoding/base64"
	"encoding/json"
	"fmt"
	"html/template"
	"io"
	"io/ioutil"
	"log"
	"net/http"
	"os"
	"os/signal"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"

	"github.com/gorilla/sessions"
	"golang.org/x/crypto/bcrypt"
	"golang.org/x/crypto/ssh"
	"golang.org/x/time/rate"
)

/* ==================== КОНСТАНТЫ ==================== */

const (
	// Шифрование
	encryptionKeySize      = 32
	randomStringCharset    = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
	defaultPasswordLength  = 20
	sessionKeyLength       = 32

	// Лимиты
	maxLogEntries          = 100
	maxFormMemory          = 10 << 20 // 10 MB
	maxHeaderBytes         = 1 << 20  // 1 MB

	// Временные интервалы
	loginRateLimitPeriod   = 2 * time.Second
	loginRateLimitAttempts = 5
	sessionMaxAge          = 86400 * 7 // 7 дней в секундах
	sshTimeout             = 30 * time.Second
	commandTimeout         = 10 * time.Second
	httpClientTimeout      = 30 * time.Second
	bruteForceDelay        = 1 * time.Second
	disconnectedCheckInterval = 10 * time.Second
	scheduleMinCheckInterval  = 1 * time.Second
	scheduleDefaultInterval   = 1 * time.Minute
	scheduleNoConnectionInterval = 30 * time.Second
	serverReadTimeout      = 15 * time.Second
	serverWriteTimeout     = 15 * time.Second
	serverIdleTimeout      = 60 * time.Second
	serverReadHeaderTimeout = 5 * time.Second
	shutdownTimeout        = 30 * time.Second

	// Значения по умолчанию
	defaultPort            = "8080"
	defaultStartHour       = 0
	defaultStartMin        = 0
	defaultEndHour         = 23
	defaultEndMin          = 0
	defaultLeasetime       = 5 // минут
	maxLeasetimeValue      = 60 // минут

	// Форматы времени
	minutesPerHour         = 60
	hoursPerDay            = 24

	// Права доступа к файлам
	configDirPerms         = 0755
	configFilePerms        = 0600
	listFilePerms          = 0644

	// Директории
	confDir                = "conf"
	listsDir               = "lists"
	configFileName         = "config.json"
	filterListFileName     = "filter.list"

	// HTTP статусы
	channelBufferSize      = 1
)

/* ==================== СТРУКТУРЫ ==================== */

type OpenWrtManager struct {
	sshClient *ssh.Client
	connected bool
	mu        sync.Mutex
}

type Settings struct {
	mu             sync.RWMutex // мьютекс для потокобезопасности
	Groups         map[string]GroupConfig `json:"groups"`
	Tags           map[string]TagConfig   `json:"tags"`
	SSHHost        string                 `json:"ssh_host,omitempty"`
	SSHUser        string                 `json:"ssh_user,omitempty"`
	SSHPass        string                 `json:"ssh_pass,omitempty"` // зашифрован AES-256-GCM
	AutoConnect    bool                   `json:"auto_connect"`
	Password       string                 `json:"password"` // bcrypt hash
	AdGuardHost    string                 `json:"adguard_host,omitempty"`
	AdGuardUser    string                 `json:"adguard_user,omitempty"`
	AdGuardPass    string                 `json:"adguard_pass,omitempty"` // зашифрованный пароль
}

type GroupConfig struct {
	Devices       []string             `json:"devices"`
	Tag           string               `json:"tag"`
	Schedule      *Schedule            `json:"schedule,omitempty"`
	DisableAction *FilterDisableAction `json:"disable_action,omitempty"`
	Leasetime     *int                 `json:"leasetime,omitempty"` // TTL в минутах, nil = по умолчанию
}

type Schedule struct {
	Enabled   bool `json:"enabled"`
	StartHour int  `json:"start_hour"`
	StartMin  int  `json:"start_min"`
	EndHour   int  `json:"end_hour"`
	EndMin    int  `json:"end_min"`
}

type FilterDisableAction struct {
	Mode string `json:"mode"` // "remove" или "switch"
	Tag  string `json:"tag,omitempty"` // тег для замены при mode="switch"
}

type TagConfig struct {
	DHCPOptions []string `json:"dhcp_options"`
}

type PageData struct {
	Connected      bool
	Settings       Settings
	GroupStates    map[string]bool
	HostStates     map[string]string
	ExistingHosts  []string
	EditingGroup   string
	EditingData    GroupConfig
	EditingTag     string
	EditingTagData TagConfig
	Message        string
	Error          string
	DarkTheme      bool
	FilterContent  string
}

type Response struct {
	Desc  string `json:"desc"`
	Level string `json:"level"`
}

type LogEntry struct {
	Time    time.Time `json:"time"`
	Message string    `json:"message"`
	Level   string    `json:"level"`
}

type AppState struct {
	mu   sync.RWMutex
	Logs []LogEntry `json:"logs"`
}

/* ==================== ГЛОБАЛЬНЫЕ ПЕРЕМЕННЫЕ ==================== */

var (
	settings             Settings
	manager              *OpenWrtManager
	darkTheme            = false
	themeMutex           sync.RWMutex
	store                *sessions.CookieStore
	appState             AppState
	encryptionKey        []byte
	loginLimiter         = rate.NewLimiter(rate.Every(loginRateLimitPeriod), loginRateLimitAttempts)
	startTime            = time.Now()
	scheduleCheckTrigger = make(chan struct{}, channelBufferSize)
)

/* ==================== ИНИЦИАЛИЗАЦИЯ ==================== */

func init() {
	// Инициализация ключа шифрования из переменной окружения
	keyEnv := os.Getenv("ENCRYPTION_KEY")
	if keyEnv == "" {
		log.Println("Warning: ENCRYPTION_KEY not set, generating random key")
		encryptionKey = make([]byte, encryptionKeySize)
		if _, err := rand.Read(encryptionKey); err != nil {
			log.Fatal("Failed to generate encryption key:", err)
		}
		encoded := base64.StdEncoding.EncodeToString(encryptionKey)
		log.Printf("⚠️  Generated encryption key (save to ENCRYPTION_KEY env): %s", encoded)
	} else {
		var err error
		encryptionKey, err = base64.StdEncoding.DecodeString(keyEnv)
		if err != nil || len(encryptionKey) != encryptionKeySize {
			log.Fatal("Invalid ENCRYPTION_KEY: must be base64-encoded 32 bytes")
		}
	}

	// Инициализация session store
	secretKey := os.Getenv("SESSION_SECRET_KEY")
	if secretKey == "" {
		log.Println("Warning: SESSION_SECRET_KEY not set, using random key")
		key, _ := generateRandomString(sessionKeyLength)
		secretKey = key
		log.Printf("⚠️  Generated session key (save to SESSION_SECRET_KEY env): %s", secretKey)
	}
	store = sessions.NewCookieStore([]byte(secretKey))
	store.Options = &sessions.Options{
		Path:     "/",
		MaxAge:   sessionMaxAge,
		HttpOnly: true,
		Secure:   os.Getenv("USE_HTTPS") == "1",
		SameSite: http.SameSiteStrictMode,
	}
}

func generateRandomString(length int) (string, error) {
	b := make([]byte, length)
	if _, err := rand.Read(b); err != nil {
		return "", fmt.Errorf("failed to generate random bytes: %w", err)
	}
	for i := range b {
		b[i] = randomStringCharset[b[i]%byte(len(randomStringCharset))]
	}
	return string(b), nil
}

func addLog(message, level string) {
	appState.mu.Lock()
	defer appState.mu.Unlock()

	entry := LogEntry{
		Time:    time.Now(),
		Message: message,
		Level:   level,
	}
	appState.Logs = append(appState.Logs, entry)

	if len(appState.Logs) > maxLogEntries {
		appState.Logs = appState.Logs[len(appState.Logs)-maxLogEntries:]
	}

	// Structured logging для production
	log.Printf("[%s] %s", strings.ToUpper(level), message)
}

func initDirectories() {
	dirs := []string{confDir, listsDir}
	for _, dir := range dirs {
		if err := os.MkdirAll(dir, configDirPerms); err != nil {
			log.Fatalf("Failed to create directory %s: %v", dir, err)
		}
	}
}

func initSettings() {
	settingsPath := filepath.Join(confDir, configFileName)

	if _, err := os.Stat(settingsPath); os.IsNotExist(err) {
		password, err := generateRandomString(defaultPasswordLength)
		if err != nil {
			log.Fatal("Error generating password:", err)
		}

		hashedPassword, err := bcrypt.GenerateFromPassword([]byte(password), bcrypt.DefaultCost)
		if err != nil {
			log.Fatal("Error generating password hash:", err)
		}

		settings = Settings{
			Groups:      make(map[string]GroupConfig),
			Tags:        make(map[string]TagConfig),
			AutoConnect: false,
			Password:    string(hashedPassword),
		}

		if err := saveSettings(); err != nil {
			log.Fatal("Error writing settings file:", err)
		}

		fmt.Printf("\n=================================================\n")
		fmt.Printf("🔑 GENERATED LOGIN PASSWORD: %s\n", password)
		fmt.Printf("=================================================\n\n")
		addLog("Application initialized with new settings", "info")
	} else {
		settingsData, err := os.ReadFile(settingsPath)
		if err != nil {
			log.Fatal("Error reading settings file:", err)
		}
		if err := json.Unmarshal(settingsData, &settings); err != nil {
			log.Fatal("Error parsing settings file:", err)
		}

		// Инициализация maps если nil
		if settings.Groups == nil {
			settings.Groups = make(map[string]GroupConfig)
		}
		if settings.Tags == nil {
			settings.Tags = make(map[string]TagConfig)
		}

		addLog("Application started", "info")
	}
}

func saveSettings() error {
	settings.mu.RLock()
	defer settings.mu.RUnlock()

	data, err := json.MarshalIndent(settings, "", "  ")
	if err != nil {
		return err
	}
	return ioutil.WriteFile(filepath.Join(confDir, configFileName), data, configFilePerms)
}

func refreshAdGuardFilters() error {
	settings.mu.RLock()
	adguardHost := settings.AdGuardHost
	adguardUser := settings.AdGuardUser
	adguardPass := settings.AdGuardPass
	settings.mu.RUnlock()

	if adguardHost == "" {
		return nil // AdGuard Home не настроен, пропускаем
	}

	// Расшифровываем пароль
	decryptedPass := ""
	if adguardPass != "" {
		var err error
		decryptedPass, err = decrypt(adguardPass)
		if err != nil {
			return fmt.Errorf("failed to decrypt AdGuard password: %w", err)
		}
	}

	// Формируем URL
	url := strings.TrimSuffix(adguardHost, "/") + "/control/filtering/refresh"

	// Создаем JSON для запроса (опциональный параметр force)
	requestBody := map[string]interface{}{
		"whitelist": false,
	}
	jsonData, err := json.Marshal(requestBody)
	if err != nil {
		return fmt.Errorf("failed to marshal request: %w", err)
	}

	// Создаем HTTP запрос
	req, err := http.NewRequest("POST", url, strings.NewReader(string(jsonData)))
	if err != nil {
		return fmt.Errorf("failed to create request: %w", err)
	}

	// Устанавливаем заголовки
	req.Header.Set("Content-Type", "application/json")

	// Добавляем Basic Auth если указаны credentials
	if adguardUser != "" && decryptedPass != "" {
		req.SetBasicAuth(adguardUser, decryptedPass)
	}

	// Выполняем запрос с таймаутом
	client := &http.Client{
		Timeout: httpClientTimeout,
	}
	resp, err := client.Do(req)
	if err != nil {
		return fmt.Errorf("failed to refresh filters: %w", err)
	}
	defer resp.Body.Close()

	// Проверяем статус ответа
	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		return fmt.Errorf("AdGuard API returned status %d: %s", resp.StatusCode, string(body))
	}

	log.Printf("AdGuard Home filters refreshed successfully")
	return nil
}

func NewOpenWrtManager() *OpenWrtManager {
	return &OpenWrtManager{
		connected: false,
	}
}

/* ==================== ШИФРОВАНИЕ ==================== */

func encrypt(plaintext string) (string, error) {
	if plaintext == "" {
		return "", nil
	}

	block, err := aes.NewCipher(encryptionKey)
	if err != nil {
		return "", err
	}

	aesGCM, err := cipher.NewGCM(block)
	if err != nil {
		return "", err
	}

	nonce := make([]byte, aesGCM.NonceSize())
	if _, err := io.ReadFull(rand.Reader, nonce); err != nil {
		return "", err
	}

	ciphertext := aesGCM.Seal(nonce, nonce, []byte(plaintext), nil)
	return base64.StdEncoding.EncodeToString(ciphertext), nil
}

func decrypt(ciphertext string) (string, error) {
	if ciphertext == "" {
		return "", nil
	}

	data, err := base64.StdEncoding.DecodeString(ciphertext)
	if err != nil {
		return "", err
	}

	block, err := aes.NewCipher(encryptionKey)
	if err != nil {
		return "", err
	}

	aesGCM, err := cipher.NewGCM(block)
	if err != nil {
		return "", err
	}

	nonceSize := aesGCM.NonceSize()
	if len(data) < nonceSize {
		return "", fmt.Errorf("ciphertext too short")
	}

	nonce, ciphertextBytes := data[:nonceSize], data[nonceSize:]
	plaintext, err := aesGCM.Open(nil, nonce, ciphertextBytes, nil)
	if err != nil {
		return "", err
	}

	return string(plaintext), nil
}

/* ==================== MIDDLEWARE ==================== */

// Middleware для проверки аутентификации
func authMiddleware(next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if !isAuthenticated(r) {
			http.Error(w, "Unauthorized", http.StatusUnauthorized)
			return
		}
		next(w, r)
	}
}

// Middleware для JSON endpoints
func jsonMiddleware(next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		next(w, r)
	}
}

// Middleware для POST-only endpoints
func postOnlyMiddleware(next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if r.Method != "POST" {
			http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
			return
		}
		next(w, r)
	}
}

// Композитный middleware для API endpoints
func apiMiddleware(handler http.HandlerFunc) http.HandlerFunc {
	return authMiddleware(jsonMiddleware(handler))
}

// Композитный middleware для API POST endpoints
func apiPostMiddleware(handler http.HandlerFunc) http.HandlerFunc {
	return authMiddleware(jsonMiddleware(postOnlyMiddleware(handler)))
}

/* ==================== АВТОРИЗАЦИЯ ==================== */

func isAuthenticated(r *http.Request) bool {
	sess, _ := store.Get(r, "session")
	v, ok := sess.Values["loggedIn"].(bool)
	return ok && v
}

func loginHandler(w http.ResponseWriter, r *http.Request) {
	if r.Method == "POST" {
		// Rate limiting для защиты от brute-force
		if !loginLimiter.Allow() {
			http.Error(w, "Too many login attempts. Please try again later.", http.StatusTooManyRequests)
			addLog("Rate limit exceeded for login attempts", "warning")
			return
		}

		pass := r.FormValue("password")

		settings.mu.RLock()
		passwordHash := settings.Password
		autoConnect := settings.AutoConnect
		sshHost := settings.SSHHost
		settings.mu.RUnlock()

		if bcrypt.CompareHashAndPassword([]byte(passwordHash), []byte(pass)) == nil {
			sess, _ := store.Get(r, "session")
			sess.Values["loggedIn"] = true
			if err := sess.Save(r, w); err != nil {
				log.Printf("Error saving session: %v", err)
				http.Error(w, "Internal server error", http.StatusInternalServerError)
				return
			}
			addLog("User logged in successfully", "info")

			// Автоподключение SSH если включено
			if autoConnect && sshHost != "" && !manager.connected {
				go func() {
					if err := manager.ensureConnection(); err != nil {
						addLog(fmt.Sprintf("SSH auto-connect failed: %v", err), "error")
					} else {
						addLog("SSH auto-connected successfully", "success")
					}
				}()
			}

			http.Redirect(w, r, "/?login=1", http.StatusFound)
			return
		} else {
			addLog("Failed login attempt", "warning")
			time.Sleep(bruteForceDelay) // Замедление для защиты от brute-force
		}
	}

	loginTemplate := `<!DOCTYPE html>
<html lang="ru">
<head>
	<meta charset="UTF-8">
	<meta name="viewport" content="width=device-width, initial-scale=1.0">
	<title>DNS Filter Manager - Вход</title>
	<style>
		*, *:before, *:after { box-sizing: border-box; }
		body {
			margin: 0; padding: 0; min-height: 100vh;
			font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
			background: #f5f5f5; display: flex; align-items: center; justify-content: center;
		}
		.login-container {
			background: white; border-radius: 8px; padding: 40px;
			box-shadow: 0 2px 10px rgba(0, 0, 0, 0.1); border: 1px solid #e0e0e0;
			width: 100%; max-width: 400px; text-align: center;
		}
		.input-group { margin-bottom: 30px; }
		.form-input {
			width: 100%; padding: 15px 20px; border: 1px solid #ddd;
			border-radius: 4px; background: white; font-size: 16px; outline: none; color: #333;
		}
		.form-input:focus { border-color: #a8d5a8; }
		.form-input::placeholder { color: #999; }
		.login-btn {
			width: 100%; padding: 15px; border: none; border-radius: 4px;
			background: #a8d5a8; color: #333; font-size: 16px; font-weight: 500; cursor: pointer;
		}
		.login-btn:hover { background: #95c695; }
		@media (max-width: 480px) {
			.login-container { margin: 20px; padding: 30px 20px; }
		}
	</style>
</head>
<body>
	<form class="login-container" method="POST">
		<div class="input-group">
			<input type="password" name="password" class="form-input" placeholder="Enter Password" autofocus required>
		</div>
		<button type="submit" class="login-btn">Войти</button>
	</form>
</body>
</html>`

	w.Header().Set("Content-Type", "text/html; charset=utf-8")
	fmt.Fprint(w, loginTemplate)
}

func logoutHandler(w http.ResponseWriter, r *http.Request) {
	sess, _ := store.Get(r, "session")
	sess.Options.MaxAge = -1
	delete(sess.Values, "loggedIn")
	if err := sess.Save(r, w); err != nil {
		log.Printf("Error clearing session: %v", err)
	}
	addLog("User logged out", "info")
	http.Redirect(w, r, "/", http.StatusFound)
}

/* ==================== SSH УПРАВЛЕНИЕ ==================== */

func (om *OpenWrtManager) ensureConnection() error {
	om.mu.Lock()
	defer om.mu.Unlock()

	if om.connected && om.sshClient != nil {
		if err := om.testConnection(); err == nil {
			return nil
		}
		om.disconnect()
	}

	settings.mu.RLock()
	sshHost := settings.SSHHost
	sshUser := settings.SSHUser
	sshPass := settings.SSHPass
	settings.mu.RUnlock()

	if sshHost != "" && sshUser != "" {
		decryptedPass, err := decrypt(sshPass)
		if err != nil {
			log.Printf("Failed to decrypt SSH password: %v", err)

			settings.mu.Lock()
			settings.SSHHost = ""
			settings.SSHUser = ""
			settings.SSHPass = ""
			settings.mu.Unlock()

			saveSettings()
			return fmt.Errorf("failed to decrypt password, credentials cleared")
		}

		// Подключаемся
		if err := om.connectSSH(sshHost, sshUser, decryptedPass); err != nil {
			return err
		}

		// Синхронизация тегов после успешного подключения
		if syncErr := om.syncTagsWithOpenWrt(); syncErr != nil {
			addLog(fmt.Sprintf("Warning: Failed to sync tags: %v", syncErr), "warning")
		}

		// Синхронизация TTL
		if syncErr := om.syncLeasetimeFromOpenWrt(); syncErr != nil {
			addLog(fmt.Sprintf("Warning: Failed to sync leasetime: %v", syncErr), "warning")
		}

		return nil
	}

	return fmt.Errorf("no SSH credentials configured")
}

func (om *OpenWrtManager) testConnection() error {
	if !om.connected || om.sshClient == nil {
		return fmt.Errorf("not connected")
	}
	session, err := om.sshClient.NewSession()
	if err != nil {
		return err
	}
	defer session.Close()

	return session.Run("echo test")
}

func (om *OpenWrtManager) disconnect() {
	if om.sshClient != nil {
		om.sshClient.Close()
	}
	om.connected = false
	om.sshClient = nil
}

func (om *OpenWrtManager) connectSSH(host, user, password string) error {
	// TODO: В production заменить на ssh.FixedHostKey или ssh.PublicKeyCallback
	// для проверки отпечатка ключа хоста и защиты от MITM атак
	config := &ssh.ClientConfig{
		User: user,
		Auth: []ssh.AuthMethod{
			ssh.Password(password),
		},
		HostKeyCallback: ssh.InsecureIgnoreHostKey(), // FIXME: небезопасно для production
		Timeout:         sshTimeout,
	}

	client, err := ssh.Dial("tcp", host, config)
	if err != nil {
		return fmt.Errorf("не удалось подключиться: %w", err)
	}

	om.sshClient = client
	om.connected = true
	return nil
}

func (om *OpenWrtManager) executeCommand(cmd string) (string, error) {
	if !om.connected {
		return "", fmt.Errorf("нет SSH подключения")
	}

	session, err := om.sshClient.NewSession()
	if err != nil {
		return "", err
	}
	defer session.Close()

	// Добавить timeout
	ctx, cancel := context.WithTimeout(context.Background(), commandTimeout)
	defer cancel()

	done := make(chan error, channelBufferSize)
	var output []byte

	go func() {
		output, err = session.Output(cmd)
		done <- err
	}()

	select {
	case <-ctx.Done():
		session.Signal(ssh.SIGKILL)
		return "", fmt.Errorf("command timeout: %s", cmd)
	case err := <-done:
		return string(output), err
	}
}

func healthHandler(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	health := map[string]interface{}{
		"status":        "ok",
		"ssh_connected": manager.connected,
		"uptime":        time.Since(startTime).String(),
	}
	json.NewEncoder(w).Encode(health)
}

func (om *OpenWrtManager) getLeasetime(hostName string) (*int, error) {
	section, err := om.getHostSection(hostName)
	if err != nil {
		return nil, err
	}

	cmd := fmt.Sprintf("uci get dhcp.%s.leasetime 2>/dev/null || echo ''", section)
	output, err := om.executeCommand(cmd)
	if err != nil {
		return nil, err
	}

	output = strings.TrimSpace(output)
	if output == "" {
		return nil, nil // По умолчанию
	}

	// Парсим значение типа "Xm"
	if strings.HasSuffix(output, "m") {
		minutesStr := strings.TrimSuffix(output, "m")
		minutes, err := strconv.Atoi(minutesStr)
		if err != nil {
			return nil, fmt.Errorf("invalid leasetime format: %s", output)
		}
		return &minutes, nil
	}

	return nil, fmt.Errorf("unsupported leasetime format: %s", output)
}

func (om *OpenWrtManager) syncLeasetimeFromOpenWrt() error {
	if !om.connected {
		return fmt.Errorf("not connected to OpenWrt")
	}

	settings.mu.Lock()
	defer settings.mu.Unlock()

	synced := false
	for groupName, groupConfig := range settings.Groups {
		if len(groupConfig.Devices) == 0 {
			continue
		}

		// Проверяем первое устройство в группе
		firstDevice := groupConfig.Devices[0]
		leasetime, err := om.getLeasetime(firstDevice)
		if err != nil {
			log.Printf("Warning: Failed to get leasetime for %s: %v", firstDevice, err)
			continue
		}

		// Обновляем только если значение отличается
		if leasetime == nil && groupConfig.Leasetime != nil {
			groupConfig.Leasetime = nil
			settings.Groups[groupName] = groupConfig
			synced = true
			log.Printf("Synced leasetime for group %s: default", groupName)
		} else if leasetime != nil && (groupConfig.Leasetime == nil || *groupConfig.Leasetime != *leasetime) {
			groupConfig.Leasetime = leasetime
			settings.Groups[groupName] = groupConfig
			synced = true
			log.Printf("Synced leasetime for group %s: %dm", groupName, *leasetime)
		}
	}

	if synced {
		// saveSettings уже содержит RLock, используем внутренний вызов
		data, err := json.MarshalIndent(settings, "", "  ")
		if err != nil {
			return fmt.Errorf("failed to save synced leasetime: %w", err)
		}
		if err := ioutil.WriteFile(filepath.Join(confDir, configFileName), data, configFilePerms); err != nil {
			return fmt.Errorf("failed to save synced leasetime: %w", err)
		}
	}

	return nil
}

func (om *OpenWrtManager) applyLeasetime(groupName string, groupConfig GroupConfig) error {
	var errors []string

	for _, hostName := range groupConfig.Devices {
		section, err := om.getHostSection(hostName)
		if err != nil {
			errors = append(errors, fmt.Sprintf("хост %s не найден", hostName))
			continue
		}

		var cmd string
		if groupConfig.Leasetime == nil {
			// Удаляем параметр leasetime
			cmd = fmt.Sprintf("uci delete dhcp.%s.leasetime 2>/dev/null || true", section)
		} else {
			// Устанавливаем leasetime
			cmd = fmt.Sprintf("uci set dhcp.%s.leasetime='%dm'", section, *groupConfig.Leasetime)
		}

		_, err = om.executeCommand(cmd)
		if err != nil {
			errors = append(errors, fmt.Sprintf("ошибка для %s: %v", hostName, err))
		}
	}

	if len(errors) > 0 {
		// Даже при ошибках пытаемся применить изменения
		om.commitChanges()
		return fmt.Errorf("ошибки: %s", strings.Join(errors, "; "))
	}

	return om.commitChanges()
}

/* ==================== SETTINGS ==================== */

func loadFilterList() string {
	filterPath := filepath.Join(listsDir, filterListFileName)
	data, err := ioutil.ReadFile(filterPath)
	if err != nil {
		return ""
	}

	// Убираем || в начале и ^ в конце для редактирования
	lines := strings.Split(string(data), "\n")
	cleanedLines := make([]string, 0, len(lines))

	for _, line := range lines {
		trimmed := strings.TrimSpace(line)

		// Пропускаем пустые строки
		if trimmed == "" {
			continue
		}

		// Сохраняем комментарии как есть
		if strings.HasPrefix(trimmed, "#") || strings.HasPrefix(trimmed, "!") {
			cleanedLines = append(cleanedLines, trimmed)
			continue
		}

		// Убираем || в начале и ^ в конце
		cleaned := strings.TrimPrefix(trimmed, "||")
		cleaned = strings.TrimSuffix(cleaned, "^")
		cleanedLines = append(cleanedLines, cleaned)
	}

	return strings.Join(cleanedLines, "\n")
}

func saveFilterList(content string) error {
	lines := strings.Split(content, "\n")
	processedLines := make([]string, 0, len(lines))

	for _, line := range lines {
		trimmed := strings.TrimSpace(line)

		// Пропускаем пустые строки
		if trimmed == "" {
			continue
		}

		// Сохраняем комментарии как есть
		if strings.HasPrefix(trimmed, "#") || strings.HasPrefix(trimmed, "!") {
			processedLines = append(processedLines, trimmed)
			continue
		}

		// Добавляем || в начало и ^ в конец, если их нет
		if !strings.HasPrefix(trimmed, "||") {
			trimmed = "||" + trimmed
		}
		if !strings.HasSuffix(trimmed, "^") {
			trimmed = trimmed + "^"
		}

		processedLines = append(processedLines, trimmed)
	}

	processedContent := strings.Join(processedLines, "\n")
	filterPath := filepath.Join(listsDir, filterListFileName)
	return ioutil.WriteFile(filterPath, []byte(processedContent), listFilePerms)
}

/* ==================== SCHEDULE ==================== */

func isFilterActiveBySchedule(schedule *Schedule) bool {
	if schedule == nil || !schedule.Enabled {
		return true
	}

	now := time.Now()
	current := now.Hour()*minutesPerHour + now.Minute()
	start := schedule.StartHour*minutesPerHour + schedule.StartMin
	end := schedule.EndHour*minutesPerHour + schedule.EndMin

	inRange := (start <= end && current >= start && current < end) ||
		(start > end && (current >= start || current < end))

	return !inRange
}

func getNextScheduleTransition(schedule *Schedule, now time.Time) time.Time {
	currentMinutes := now.Hour()*minutesPerHour + now.Minute()
	startMinutes := schedule.StartHour*minutesPerHour + schedule.StartMin
	endMinutes := schedule.EndHour*minutesPerHour + schedule.EndMin

	var nextTransitionMinutes int
	today := time.Date(now.Year(), now.Month(), now.Day(), 0, 0, 0, 0, now.Location())

	if startMinutes <= endMinutes {
		// Обычное расписание (в пределах одного дня)
		if currentMinutes < startMinutes {
			nextTransitionMinutes = startMinutes
		} else if currentMinutes < endMinutes {
			nextTransitionMinutes = endMinutes
		} else {
			// Следующий переход завтра утром
			return today.Add(hoursPerDay*time.Hour + time.Duration(startMinutes)*time.Minute)
		}
	} else {
		// Расписание через полночь
		if currentMinutes < endMinutes {
			nextTransitionMinutes = endMinutes
		} else if currentMinutes < startMinutes {
			nextTransitionMinutes = startMinutes
		} else {
			// Следующий переход завтра
			return today.Add(hoursPerDay*time.Hour + time.Duration(endMinutes)*time.Minute)
		}
	}

	return today.Add(time.Duration(nextTransitionMinutes) * time.Minute)
}

// Функция для инициирования немедленной проверки расписания
func triggerScheduleCheck() {
	select {
	case scheduleCheckTrigger <- struct{}{}:
		log.Println("Запланирована немедленная проверка расписания")
	default:
		// Канал уже заполнен, проверка уже запланирована
	}
}

// Проверяет и применяет расписания для всех групп
func (om *OpenWrtManager) checkAndApplySchedules() {
	if !om.connected {
		return
	}

	// Получаем состояния один раз для всех групп
	groupStates, _, err := om.getGroupStates()
	if err != nil {
		log.Printf("Ошибка получения состояния групп: %v", err)
		return
	}

	settings.mu.RLock()
	groups := make(map[string]GroupConfig)
	for k, v := range settings.Groups {
		groups[k] = v
	}
	settings.mu.RUnlock()

	for groupName, groupConfig := range groups {
		if groupConfig.Schedule != nil && groupConfig.Schedule.Enabled {
			shouldBeActive := isFilterActiveBySchedule(groupConfig.Schedule)
			currentlyActive := groupStates[groupName]

			if shouldBeActive != currentlyActive {
				err := om.setGroupTag(groupName, shouldBeActive)
				if err != nil {
					log.Printf("Ошибка автоматического управления группой %s: %v", groupName, err)
				} else {
					status := "включена (вне времени отключения)"
					if !shouldBeActive {
						status = "отключена (время отключения)"
					}
					addLog(fmt.Sprintf("Группа %s автоматически %s по расписанию", groupName, status), "info")
				}
			}
		}
	}
}

// Вычисляет время до следующего события расписания
func (om *OpenWrtManager) getNextScheduleTime() time.Duration {
	if !om.connected {
		return disconnectedCheckInterval
	}

	now := time.Now()
	var nextEventTime *time.Time

	settings.mu.RLock()
	for _, groupConfig := range settings.Groups {
		if groupConfig.Schedule != nil && groupConfig.Schedule.Enabled {
			nextTime := getNextScheduleTransition(groupConfig.Schedule, now)
			if nextEventTime == nil || nextTime.Before(*nextEventTime) {
				nextEventTime = &nextTime
			}
		}
	}
	settings.mu.RUnlock()

	if nextEventTime != nil {
		duration := time.Until(*nextEventTime)
		if duration < scheduleMinCheckInterval {
			duration = scheduleMinCheckInterval
		}
		log.Printf("Следующая проверка расписания через %v", duration)
		return duration
	}

	return scheduleDefaultInterval
}

/* ==================== OPENWRT OPERATIONS ==================== */

func (om *OpenWrtManager) getHostsInfo() (map[string]map[string]string, error) {
	cmd := "uci show dhcp | grep '@host\\[' | grep -E '\\.(name|ip|mac|tag)='"
	output, err := om.executeCommand(cmd)
	if err != nil {
		return nil, err
	}

	hosts := make(map[string]map[string]string)
	lines := strings.Split(strings.TrimSpace(output), "\n")

	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}

		parts := strings.Split(line, "=")
		if len(parts) != 2 {
			continue
		}

		configPart := parts[0]
		value := strings.Trim(parts[1], "'\"")

		configParts := strings.Split(configPart, ".")
		if len(configParts) < 3 {
			continue
		}

		section := configParts[1]
		param := configParts[2]

		if hosts[section] == nil {
			hosts[section] = make(map[string]string)
		}
		hosts[section][param] = value
	}

	return hosts, nil
}

func (om *OpenWrtManager) getExistingHosts() ([]string, error) {
	hostsInfo, err := om.getHostsInfo()
	if err != nil {
		return nil, err
	}

	var hostNames []string
	for _, hostData := range hostsInfo {
		if name, exists := hostData["name"]; exists {
			hostNames = append(hostNames, name)
		}
	}

	sort.Strings(hostNames)
	return hostNames, nil
}

func (om *OpenWrtManager) getExistingTags() (map[string]TagConfig, error) {
	tags := make(map[string]TagConfig)

	// Получаем только именованные секции тегов (не анонимные @tag[X])
	cmd := "uci show dhcp | grep \"^dhcp\\.[^@][^.]*=tag$\" | cut -d'.' -f2 | cut -d'=' -f1"
	output, err := om.executeCommand(cmd)
	if err != nil {
		return tags, nil
	}

	tagNames := strings.Split(strings.TrimSpace(output), "\n")

	for _, tagName := range tagNames {
		tagName = strings.TrimSpace(tagName)
		if tagName == "" {
			continue
		}

		// Получаем DHCP опции для именованного тега
		optionsCmd := fmt.Sprintf("uci get dhcp.%s.dhcp_option 2>/dev/null || echo ''", tagName)
		optionsOutput, err := om.executeCommand(optionsCmd)
		if err != nil {
			continue
		}

		var options []string
		optionsStr := strings.TrimSpace(optionsOutput)
		if optionsStr != "" {
			// Опции могут быть в формате 'option1' 'option2' или просто список
			optionsStr = strings.Trim(optionsStr, "'")

			// Если несколько опций через пробел с кавычками
			if strings.Contains(optionsStr, "' '") {
				parts := strings.Split(optionsStr, "' '")
				for _, opt := range parts {
					opt = strings.TrimSpace(strings.Trim(opt, "'"))
					if opt != "" {
						options = append(options, opt)
					}
				}
			} else {
				// Одна опция
				options = append(options, optionsStr)
			}
		}

		if len(options) > 0 {
			tags[tagName] = TagConfig{DHCPOptions: options}
		}
	}

	return tags, nil
}

func (om *OpenWrtManager) syncTagsWithOpenWrt() error {
	if !om.connected {
		return fmt.Errorf("not connected to OpenWrt")
	}

	existingTags, err := om.getExistingTags()
	if err != nil {
		return fmt.Errorf("failed to read tags from OpenWrt: %w", err)
	}

	settings.mu.Lock()
	defer settings.mu.Unlock()

	// Объединяем теги: приоритет у локальных настроек
	synced := false
	for tagName, tagConfig := range existingTags {
		if _, exists := settings.Tags[tagName]; !exists {
			settings.Tags[tagName] = tagConfig
			synced = true
			addLog(fmt.Sprintf("Импортирован тег из OpenWrt: %s", tagName), "info")
		}
	}

	if synced {
		// Внутренний вызов сохранения (без дополнительной блокировки)
		data, err := json.MarshalIndent(settings, "", "  ")
		if err != nil {
			return fmt.Errorf("failed to save synced tags: %w", err)
		}
		if err := ioutil.WriteFile(filepath.Join(confDir, configFileName), data, configFilePerms); err != nil {
			return fmt.Errorf("failed to save synced tags: %w", err)
		}
	}

	return nil
}

func (om *OpenWrtManager) getHostSection(hostName string) (string, error) {
	hostsInfo, err := om.getHostsInfo()
	if err != nil {
		return "", err
	}

	for section, hostData := range hostsInfo {
		if hostData["name"] == hostName {
			return section, nil
		}
	}

	return "", fmt.Errorf("хост %s не найден", hostName)
}

func (om *OpenWrtManager) hostExists(hostName string) bool {
	_, err := om.getHostSection(hostName)
	return err == nil
}

func (om *OpenWrtManager) getHostTagState(hostName string) string {
	section, err := om.getHostSection(hostName)
	if err != nil {
		return "not-exists"
	}

	cmd := fmt.Sprintf("uci get dhcp.%s.tag 2>/dev/null || echo 'no-tag'", section)
	output, err := om.executeCommand(cmd)
	if err != nil {
		return "error"
	}
	output = strings.TrimSpace(output)
	if output == "no-tag" || output == "" {
		return "no-tag"
	}
	return output
}

func (om *OpenWrtManager) getGroupStates() (map[string]bool, map[string]string, error) {
	groupStates := make(map[string]bool)
	hostStates := make(map[string]string)

	settings.mu.RLock()
	groups := make(map[string]GroupConfig)
	for k, v := range settings.Groups {
		groups[k] = v
	}
	settings.mu.RUnlock()

	for groupName, groupConfig := range groups {
		hasActiveTag := false
		for _, hostName := range groupConfig.Devices {
			if om.hostExists(hostName) {
				state := om.getHostTagState(hostName)
				hostStates[hostName] = state
				if state == groupConfig.Tag {
					hasActiveTag = true
				}
			} else {
				hostStates[hostName] = "not-exists"
			}
		}
		groupStates[groupName] = hasActiveTag
	}

	return groupStates, hostStates, nil
}

func (om *OpenWrtManager) createTag(tagName string, dhcpOptions []string) error {
	checkCmd := fmt.Sprintf("uci get dhcp.%s 2>/dev/null", tagName)
	_, err := om.executeCommand(checkCmd)
	if err == nil {
		return fmt.Errorf("тег %s уже существует в конфигурации", tagName)
	}

	_, err = om.executeCommand(fmt.Sprintf("uci set dhcp.%s=tag", tagName))
	if err != nil {
		return fmt.Errorf("ошибка создания тега: %w", err)
	}

	for _, option := range dhcpOptions {
		_, err = om.executeCommand(fmt.Sprintf("uci add_list dhcp.%s.dhcp_option='%s'", tagName, option))
		if err != nil {
			return fmt.Errorf("ошибка добавления опции %s: %w", option, err)
		}
	}

	return om.commitChanges()
}

func (om *OpenWrtManager) deleteTag(tagName string) error {
	checkCmd := fmt.Sprintf("uci get dhcp.%s 2>/dev/null", tagName)
	_, err := om.executeCommand(checkCmd)
	if err != nil {
		return fmt.Errorf("тег %s не найден в конфигурации", tagName)
	}

	_, err = om.executeCommand(fmt.Sprintf("uci delete dhcp.%s", tagName))
	if err != nil {
		return fmt.Errorf("ошибка удаления тега: %w", err)
	}

	return om.commitChanges()
}

func (om *OpenWrtManager) setGroupTag(groupName string, enabled bool) error {
	settings.mu.RLock()
	groupConfig, exists := settings.Groups[groupName]
	settings.mu.RUnlock()

	if !exists {
		return fmt.Errorf("группа не найдена")
	}

	var errors []string
	var successCount int

	for _, hostName := range groupConfig.Devices {
		section, err := om.getHostSection(hostName)
		if err != nil {
			errors = append(errors, fmt.Sprintf("хост %s не найден", hostName))
			continue
		}

		var cmd string
		if enabled {
			cmd = fmt.Sprintf("uci set dhcp.%s.tag='%s'", section, groupConfig.Tag)
		} else {
			// Проверяем настройки действия при отключении
			if groupConfig.DisableAction != nil && groupConfig.DisableAction.Mode == "switch" && groupConfig.DisableAction.Tag != "" {
				// Заменяем на альтернативный тег
				cmd = fmt.Sprintf("uci set dhcp.%s.tag='%s'", section, groupConfig.DisableAction.Tag)
			} else {
				// Удаляем тег (поведение по умолчанию)
				cmd = fmt.Sprintf("uci delete dhcp.%s.tag 2>/dev/null || true", section)
			}
		}

		_, err = om.executeCommand(cmd)
		if err != nil {
			errors = append(errors, fmt.Sprintf("ошибка для %s: %v", hostName, err))
		} else {
			successCount++
		}
	}

	if successCount > 0 {
		if err := om.commitChanges(); err != nil {
			return err
		}
	}

	if len(errors) > 0 {
		if successCount > 0 {
			return fmt.Errorf("частичный успех (%d/%d): %s", successCount, len(groupConfig.Devices), strings.Join(errors, "; "))
		}
		return fmt.Errorf("ошибки: %s", strings.Join(errors, "; "))
	}

	return nil
}

func (om *OpenWrtManager) setTagOnDevice(hostName, tagName string) error {
	section, err := om.getHostSection(hostName)
	if err != nil {
		return fmt.Errorf("хост %s не найден", hostName)
	}

	cmd := fmt.Sprintf("uci set dhcp.%s.tag='%s'", section, tagName)
	_, err = om.executeCommand(cmd)
	if err != nil {
		return fmt.Errorf("ошибка установки тега на %s: %v", hostName, err)
	}

	return nil
}

func (om *OpenWrtManager) removeTagFromDevice(hostName, tagName string) error {
	section, err := om.getHostSection(hostName)
	if err != nil {
		return fmt.Errorf("хост %s не найден", hostName)
	}

	currentTag := om.getHostTagState(hostName)
	if currentTag == tagName {
		cmd := fmt.Sprintf("uci delete dhcp.%s.tag 2>/dev/null || true", section)
		_, err = om.executeCommand(cmd)
		if err != nil {
			return fmt.Errorf("ошибка удаления тега с %s: %v", hostName, err)
		}
	}

	return nil
}

func (om *OpenWrtManager) setTagsOnNewDevices(groupName string, oldDevices, newDevices []string, tag string) error {
	var errors []string
	var successCount int

	oldDeviceMap := make(map[string]bool)
	for _, device := range oldDevices {
		oldDeviceMap[device] = true
	}

	for _, device := range newDevices {
		if !oldDeviceMap[device] {
			err := om.setTagOnDevice(device, tag)
			if err != nil {
				errors = append(errors, err.Error())
			} else {
				successCount++
			}
		}
	}

	if successCount > 0 {
		if err := om.commitChanges(); err != nil {
			return err
		}
	}

	if len(errors) > 0 {
		return fmt.Errorf("ошибки при установке тегов: %s", strings.Join(errors, "; "))
	}

	return nil
}

func (om *OpenWrtManager) updateGroupDevices(groupName string, oldDevices, newDevices []string, tag string) error {
	var errors []string
	var successCount int

	oldDeviceMap := make(map[string]bool)
	for _, device := range oldDevices {
		oldDeviceMap[device] = true
	}

	newDeviceMap := make(map[string]bool)
	for _, device := range newDevices {
		newDeviceMap[device] = true
	}

	for _, device := range oldDevices {
		if !newDeviceMap[device] {
			err := om.removeTagFromDevice(device, tag)
			if err != nil {
				errors = append(errors, err.Error())
			} else {
				successCount++
			}
		}
	}

	if successCount > 0 {
		if err := om.commitChanges(); err != nil {
			return err
		}
	}

	if len(errors) > 0 {
		return fmt.Errorf("ошибки при удалении тегов: %s", strings.Join(errors, "; "))
	}

	return nil
}

func (om *OpenWrtManager) commitChanges() error {
	_, err := om.executeCommand("uci commit dhcp")
	if err != nil {
		return fmt.Errorf("ошибка сохранения: %w", err)
	}

	_, err = om.executeCommand("/etc/init.d/dnsmasq reload")
	if err != nil {
		return fmt.Errorf("ошибка перезапуска dnsmasq: %w", err)
	}

	return nil
}

/* ==================== HTTP HANDLERS ==================== */

func themeHandler(w http.ResponseWriter, r *http.Request) {
	theme := r.FormValue("theme")

	themeMutex.Lock()
	darkTheme = theme == "dark"
	themeMutex.Unlock()

	response := Response{Desc: "Theme updated", Level: "success"}
	json.NewEncoder(w).Encode(response)
}

func statusHandler(w http.ResponseWriter, r *http.Request) {
	json.NewEncoder(w).Encode(map[string]bool{
		"connected": manager.connected,
	})
}

func scheduleGetHandler(w http.ResponseWriter, r *http.Request) {
	groupName := strings.TrimPrefix(r.URL.Path, "/api/schedule/")

	settings.mu.RLock()
	groupConfig, exists := settings.Groups[groupName]
	settings.mu.RUnlock()

	if exists && groupConfig.Schedule != nil {
		json.NewEncoder(w).Encode(groupConfig.Schedule)
	} else {
		defaultSchedule := Schedule{
			Enabled:   false,
			StartHour: defaultStartHour,
			StartMin:  defaultStartMin,
			EndHour:   defaultEndHour,
			EndMin:    defaultEndMin,
		}
		json.NewEncoder(w).Encode(defaultSchedule)
	}
}

func scheduleSaveHandler(w http.ResponseWriter, r *http.Request) {
	groupName := r.FormValue("group_name")
	enabled := r.FormValue("enabled") == "true"
	startHour, _ := strconv.Atoi(r.FormValue("start_hour"))
	startMin, _ := strconv.Atoi(r.FormValue("start_min"))
	endHour, _ := strconv.Atoi(r.FormValue("end_hour"))
	endMin, _ := strconv.Atoi(r.FormValue("end_min"))

	settings.mu.Lock()
	groupConfig, exists := settings.Groups[groupName]
	if exists {
		groupConfig.Schedule = &Schedule{
			Enabled:   enabled,
			StartHour: startHour,
			StartMin:  startMin,
			EndHour:   endHour,
			EndMin:    endMin,
		}
		settings.Groups[groupName] = groupConfig
	}
	settings.mu.Unlock()

	if !exists {
		response := Response{Desc: "Группа не найдена", Level: "error"}
		json.NewEncoder(w).Encode(response)
		return
	}

	if err := saveSettings(); err != nil {
		response := Response{Desc: fmt.Sprintf("Ошибка сохранения: %v", err), Level: "error"}
		json.NewEncoder(w).Encode(response)
	} else {
		triggerScheduleCheck()
		response := Response{Desc: "Расписание сохранено", Level: "success"}
		json.NewEncoder(w).Encode(response)
	}
}

func scheduleToggleHandler(w http.ResponseWriter, r *http.Request) {
	groupName := r.FormValue("group")
	enabled := r.FormValue("enabled") == "true"

	settings.mu.Lock()
	groupConfig, exists := settings.Groups[groupName]
	if exists {
		if groupConfig.Schedule == nil {
			groupConfig.Schedule = &Schedule{
				Enabled:   false,
				StartHour: defaultStartHour,
				StartMin:  defaultStartMin,
				EndHour:   defaultEndHour,
				EndMin:    defaultEndMin,
			}
		}
		groupConfig.Schedule.Enabled = enabled
		settings.Groups[groupName] = groupConfig
	}
	settings.mu.Unlock()

	if !exists {
		response := Response{Desc: "Группа не найдена", Level: "error"}
		json.NewEncoder(w).Encode(response)
		return
	}

	if err := saveSettings(); err != nil {
		response := Response{Desc: fmt.Sprintf("Ошибка сохранения: %v", err), Level: "error"}
		json.NewEncoder(w).Encode(response)
	} else {
		triggerScheduleCheck()
		status := "выключено"
		if enabled {
			status = "включено"
		}
		response := Response{Desc: fmt.Sprintf("Расписание группы %s %s", groupName, status), Level: "success"}
		json.NewEncoder(w).Encode(response)
	}
}

func disableActionGetHandler(w http.ResponseWriter, r *http.Request) {
	groupName := strings.TrimPrefix(r.URL.Path, "/api/disable-action/")

	settings.mu.RLock()
	groupConfig, exists := settings.Groups[groupName]
	settings.mu.RUnlock()

	if exists && groupConfig.DisableAction != nil {
		json.NewEncoder(w).Encode(groupConfig.DisableAction)
	} else {
		defaultAction := FilterDisableAction{
			Mode: "remove",
			Tag:  "",
		}
		json.NewEncoder(w).Encode(defaultAction)
	}
}

func disableActionSaveHandler(w http.ResponseWriter, r *http.Request) {
	groupName := r.FormValue("group_name")
	mode := r.FormValue("mode")
	tag := r.FormValue("tag")

	settings.mu.Lock()
	groupConfig, exists := settings.Groups[groupName]
	if exists {
		groupConfig.DisableAction = &FilterDisableAction{
			Mode: mode,
			Tag:  tag,
		}
		settings.Groups[groupName] = groupConfig
	}
	settings.mu.Unlock()

	if !exists {
		response := Response{Desc: "Группа не найдена", Level: "error"}
		json.NewEncoder(w).Encode(response)
		return
	}

	if err := saveSettings(); err != nil {
		response := Response{Desc: fmt.Sprintf("Ошибка сохранения: %v", err), Level: "error"}
		json.NewEncoder(w).Encode(response)
	} else {
		response := Response{Desc: "Настройки действия сохранены", Level: "success"}
		json.NewEncoder(w).Encode(response)
	}
}

func leasetimeGetHandler(w http.ResponseWriter, r *http.Request) {
	groupName := strings.TrimPrefix(r.URL.Path, "/api/leasetime/")

	settings.mu.RLock()
	groupConfig, exists := settings.Groups[groupName]
	settings.mu.RUnlock()

	if exists && groupConfig.Leasetime != nil {
		json.NewEncoder(w).Encode(map[string]interface{}{
			"leasetime": *groupConfig.Leasetime,
			"mode":      "custom",
		})
	} else {
		json.NewEncoder(w).Encode(map[string]interface{}{
			"leasetime": defaultLeasetime,
			"mode":      "default",
		})
	}
}

func leasetimeSaveHandler(w http.ResponseWriter, r *http.Request) {
	groupName := r.FormValue("group_name")
	mode := r.FormValue("mode")
	leasetimeStr := r.FormValue("leasetime")

	settings.mu.Lock()
	groupConfig, exists := settings.Groups[groupName]
	if exists {
		if mode == "default" {
			groupConfig.Leasetime = nil
		} else {
			leasetime, err := strconv.Atoi(leasetimeStr)
			if err != nil || leasetime < 0 || leasetime > maxLeasetimeValue {
				settings.mu.Unlock()
				response := Response{Desc: fmt.Sprintf("Некорректное значение срока аренды (0-%d минут)", maxLeasetimeValue), Level: "error"}
				json.NewEncoder(w).Encode(response)
				return
			}
			groupConfig.Leasetime = &leasetime
		}
		settings.Groups[groupName] = groupConfig
	}
	settings.mu.Unlock()

	if !exists {
		response := Response{Desc: "Группа не найдена", Level: "error"}
		json.NewEncoder(w).Encode(response)
		return
	}

	if err := saveSettings(); err != nil {
		response := Response{Desc: fmt.Sprintf("Ошибка сохранения: %v", err), Level: "error"}
		json.NewEncoder(w).Encode(response)
	} else {
		// Применяем изменения в OpenWrt если подключены
		if manager.connected {
			if err := manager.applyLeasetime(groupName, groupConfig); err != nil {
				log.Printf("Warning: Failed to apply leasetime: %v", err)
			}
		}
		response := Response{Desc: "Настройки срока аренды сохранены", Level: "success"}
		json.NewEncoder(w).Encode(response)
	}
}

func adguardSettingsHandler(w http.ResponseWriter, r *http.Request) {
	newHost := r.FormValue("adguard_host")
	newUser := r.FormValue("adguard_user")
	newPass := r.FormValue("adguard_pass")

	settings.mu.Lock()
	settings.AdGuardHost = newHost
	settings.AdGuardUser = newUser

	// Шифруем пароль если он указан
	if newPass != "" {
		encryptedPass, err := encrypt(newPass)
		if err != nil {
			settings.mu.Unlock()
			json.NewEncoder(w).Encode(Response{
				Desc:  fmt.Sprintf("Ошибка шифрования пароля: %v", err),
				Level: "error",
			})
			return
		}
		settings.AdGuardPass = encryptedPass
	}
	settings.mu.Unlock()

	if err := saveSettings(); err != nil {
		json.NewEncoder(w).Encode(Response{
			Desc:  fmt.Sprintf("Ошибка сохранения: %v", err),
			Level: "error",
		})
		return
	}

	json.NewEncoder(w).Encode(Response{
		Desc:  "Настройки AdGuard Home сохранены",
		Level: "success",
	})
}

func adguardTestHandler(w http.ResponseWriter, r *http.Request) {
	if err := refreshAdGuardFilters(); err != nil {
		json.NewEncoder(w).Encode(Response{
			Desc:  fmt.Sprintf("Ошибка: %v", err),
			Level: "error",
		})
		return
	}

	json.NewEncoder(w).Encode(Response{
		Desc:  "Подключение успешно! Фильтры обновлены.",
		Level: "success",
	})
}

func connectHandler(w http.ResponseWriter, r *http.Request) {
	if !isAuthenticated(r) {
		http.Redirect(w, r, "/", http.StatusFound)
		return
	}

	if r.Method == "POST" {
		host := strings.TrimSpace(r.FormValue("host"))
		user := strings.TrimSpace(r.FormValue("user"))
		password := r.FormValue("password")
		autoConnect := r.FormValue("auto_connect") == "on"

		if host == "" || user == "" || password == "" {
			http.Redirect(w, r, "/?error=missing_fields", http.StatusFound)
			return
		}

		err := manager.connectSSH(host, user, password)

		if err == nil {
			// Шифруем пароль перед сохранением
			encryptedPass, encErr := encrypt(password)
			if encErr != nil {
				addLog(fmt.Sprintf("Failed to encrypt password: %v", encErr), "error")
				http.Redirect(w, r, "/?error=encryption_failed", http.StatusFound)
				return
			}

			// Сохраняем учётные данные
			settings.mu.Lock()
			settings.SSHHost = host
			settings.SSHUser = user
			settings.SSHPass = encryptedPass
			settings.AutoConnect = autoConnect
			settings.mu.Unlock()

			if saveErr := saveSettings(); saveErr != nil {
				addLog(fmt.Sprintf("Failed to save settings: %v", saveErr), "error")
			} else {
				addLog(fmt.Sprintf("SSH connected and credentials saved (AutoConnect: %v)", autoConnect), "success")
				if syncErr := manager.syncTagsWithOpenWrt(); syncErr != nil {
					addLog(fmt.Sprintf("Warning: Failed to sync tags: %v", syncErr), "warning")
				}
			}
		} else {
			addLog(fmt.Sprintf("SSH connection failed: %v", err), "error")
		}
	}

	http.Redirect(w, r, "/", http.StatusFound)
}

func disconnectHandler(w http.ResponseWriter, r *http.Request) {
	if !isAuthenticated(r) {
		http.Redirect(w, r, "/", http.StatusFound)
		return
	}

	manager.mu.Lock()
	manager.disconnect()
	manager.mu.Unlock()

	addLog("SSH disconnected", "info")
	http.Redirect(w, r, "/", http.StatusFound)
}

func toggleHandler(w http.ResponseWriter, r *http.Request) {
	group := r.FormValue("group")

	if !manager.connected {
		response := Response{Desc: "Нет подключения к роутеру", Level: "error"}
		json.NewEncoder(w).Encode(response)
		return
	}

	groupStates, _, _ := manager.getGroupStates()
	currentState := groupStates[group]
	newState := !currentState

	err := manager.setGroupTag(group, newState)
	if err != nil {
		response := Response{Desc: fmt.Sprintf("Ошибка: %v", err), Level: "error"}
		json.NewEncoder(w).Encode(response)
	} else {
		// Отключаем расписание при ручном переключении
		settings.mu.Lock()
		groupConfig, exists := settings.Groups[group]
		if exists && groupConfig.Schedule != nil && groupConfig.Schedule.Enabled {
			groupConfig.Schedule.Enabled = false
			settings.Groups[group] = groupConfig
			settings.mu.Unlock()

			if saveErr := saveSettings(); saveErr != nil {
				log.Printf("Warning: Failed to save schedule state: %v", saveErr)
			}
			addLog(fmt.Sprintf("Расписание группы %s отключено (переход на ручное управление)", group), "info")
		} else {
			settings.mu.Unlock()
		}

		status := "выключена"
		if newState {
			status = "включена"
		}
		response := Response{Desc: fmt.Sprintf("Группа %s %s", group, status), Level: "success"}
		json.NewEncoder(w).Encode(response)
	}
}

func removeDeviceFromGroupsHandler(w http.ResponseWriter, r *http.Request) {
	deviceName := r.FormValue("device")

	if deviceName == "" {
		json.NewEncoder(w).Encode(Response{Desc: "Имя устройства не указано", Level: "error"})
		return
	}

	// Удаляем устройство из всех групп
	settings.mu.Lock()
	removedFrom := []string{}
	for groupName, groupConfig := range settings.Groups {
		newDevices := []string{}
		found := false
		for _, device := range groupConfig.Devices {
			if device != deviceName {
				newDevices = append(newDevices, device)
			} else {
				found = true
			}
		}

		if found {
			groupConfig.Devices = newDevices
			settings.Groups[groupName] = groupConfig
			removedFrom = append(removedFrom, groupName)
		}
	}
	settings.mu.Unlock()

	if len(removedFrom) == 0 {
		json.NewEncoder(w).Encode(Response{Desc: fmt.Sprintf("Устройство %s не найдено ни в одной группе", deviceName), Level: "warning"})
		return
	}

	if err := saveSettings(); err != nil {
		json.NewEncoder(w).Encode(Response{Desc: fmt.Sprintf("Ошибка сохранения: %v", err), Level: "error"})
		return
	}

	msg := fmt.Sprintf("Устройство %s удалено из групп: %s", deviceName, strings.Join(removedFrom, ", "))
	addLog(msg, "info")
	json.NewEncoder(w).Encode(Response{Desc: msg, Level: "success"})
}

func createTagHandler(w http.ResponseWriter, r *http.Request) {
	// Для multipart/form-data используем ParseMultipartForm вместо ParseForm
	if err := r.ParseMultipartForm(maxFormMemory); err != nil {
		// Если не multipart, пробуем ParseForm
		if err := r.ParseForm(); err != nil {
			response := Response{Desc: fmt.Sprintf("Ошибка парсинга формы: %v", err), Level: "error"}
			json.NewEncoder(w).Encode(response)
			return
		}
	}

	// Теперь получаем и очищаем значения
	tagName := strings.TrimSpace(r.FormValue("tagname"))
	dhcpOptionsStr := strings.TrimSpace(r.FormValue("dhcpoptions"))

	// Проверка заполнения полей
	if tagName == "" || dhcpOptionsStr == "" {
		response := Response{Desc: "Заполните все поля", Level: "error"}
		json.NewEncoder(w).Encode(response)
		return
	}

	// Проверка на существование тега
	settings.mu.RLock()
	_, exists := settings.Tags[tagName]
	settings.mu.RUnlock()

	if exists {
		response := Response{Desc: fmt.Sprintf("Тег '%s' уже существует", tagName), Level: "error"}
		json.NewEncoder(w).Encode(response)
		return
	}

	// Парсинг DHCP опций
	var options []string
	for _, line := range strings.Split(dhcpOptionsStr, "\n") {
		opt := strings.TrimSpace(line)
		if opt != "" {
			options = append(options, opt)
		}
	}

	if len(options) == 0 {
		response := Response{Desc: "Добавьте хотя бы одну DHCP опцию", Level: "error"}
		json.NewEncoder(w).Encode(response)
		return
	}

	// Создание тега в OpenWrt
	if err := manager.createTag(tagName, options); err != nil {
		response := Response{Desc: fmt.Sprintf("Ошибка создания тега: %v", err), Level: "error"}
		json.NewEncoder(w).Encode(response)
	} else {
		settings.mu.Lock()
		settings.Tags[tagName] = TagConfig{DHCPOptions: options}
		settings.mu.Unlock()

		if err := saveSettings(); err != nil {
			response := Response{Desc: fmt.Sprintf("Ошибка сохранения: %v", err), Level: "error"}
			json.NewEncoder(w).Encode(response)
		} else {
			response := Response{Desc: fmt.Sprintf("Тег '%s' создан (%d опций)", tagName, len(options)), Level: "success"}
			json.NewEncoder(w).Encode(response)
		}
	}
}

func deleteTagHandler(w http.ResponseWriter, r *http.Request) {
	tagName := r.FormValue("tag_name")

	settings.mu.RLock()
	_, exists := settings.Tags[tagName]
	settings.mu.RUnlock()

	if !exists {
		response := Response{Desc: fmt.Sprintf("Тег %s не найден", tagName), Level: "error"}
		json.NewEncoder(w).Encode(response)
		return
	}

	if err := manager.deleteTag(tagName); err != nil {
		response := Response{Desc: fmt.Sprintf("Ошибка удаления тега: %v", err), Level: "error"}
		json.NewEncoder(w).Encode(response)
	} else {
		settings.mu.Lock()
		delete(settings.Tags, tagName)
		settings.mu.Unlock()

		if err := saveSettings(); err != nil {
			response := Response{Desc: fmt.Sprintf("Ошибка сохранения: %v", err), Level: "error"}
			json.NewEncoder(w).Encode(response)
		} else {
			response := Response{Desc: fmt.Sprintf("Тег %s удалён", tagName), Level: "success"}
			json.NewEncoder(w).Encode(response)
		}
	}
}

func createGroupHandler(w http.ResponseWriter, r *http.Request) {
	if err := r.ParseMultipartForm(maxFormMemory); err != nil {
		if err := r.ParseForm(); err != nil {
			response := Response{Desc: fmt.Sprintf("Ошибка парсинга формы: %v", err), Level: "error"}
			json.NewEncoder(w).Encode(response)
			return
		}
	}

	groupName := strings.TrimSpace(r.FormValue("groupname"))
	tag := strings.TrimSpace(r.FormValue("tag"))

	if groupName == "" || tag == "" {
		response := Response{Desc: "Заполните все поля", Level: "error"}
		json.NewEncoder(w).Encode(response)
		return
	}

	settings.mu.RLock()
	_, exists := settings.Groups[groupName]
	settings.mu.RUnlock()

	if exists {
		response := Response{Desc: fmt.Sprintf("Группа '%s' уже существует", groupName), Level: "error"}
		json.NewEncoder(w).Encode(response)
		return
	}

	var devices []string
	devices = r.Form["devices"]

	settings.mu.Lock()
	settings.Groups[groupName] = GroupConfig{
		Devices: devices,
		Tag:     tag,
	}
	settings.mu.Unlock()

	if err := saveSettings(); err != nil {
		response := Response{Desc: fmt.Sprintf("Ошибка сохранения: %v", err), Level: "error"}
		json.NewEncoder(w).Encode(response)
	} else {
		response := Response{Desc: fmt.Sprintf("Группа '%s' создана", groupName), Level: "success"}
		json.NewEncoder(w).Encode(response)
	}
}

func updateGroupHandler(w http.ResponseWriter, r *http.Request) {
	if err := r.ParseMultipartForm(maxFormMemory); err != nil {
		if err := r.ParseForm(); err != nil {
			response := Response{Desc: fmt.Sprintf("Ошибка парсинга формы: %v", err), Level: "error"}
			json.NewEncoder(w).Encode(response)
			return
		}
	}

	groupName := r.FormValue("groupname")
	tag := strings.TrimSpace(r.FormValue("tag"))

	if groupName == "" || tag == "" {
		response := Response{Desc: "Заполните все поля", Level: "error"}
		json.NewEncoder(w).Encode(response)
		return
	}

	settings.mu.RLock()
	oldGroupConfig, exists := settings.Groups[groupName]
	settings.mu.RUnlock()

	if !exists {
		response := Response{Desc: fmt.Sprintf("Группа '%s' не найдена", groupName), Level: "error"}
		json.NewEncoder(w).Encode(response)
		return
	}

	var devices []string
	devices = r.Form["devices"]

	// Обновление устройств в OpenWrt
	if manager.connected {
		if err := manager.updateGroupDevices(groupName, oldGroupConfig.Devices, devices, oldGroupConfig.Tag); err != nil {
			log.Printf("Ошибка удаления тегов со старых устройств: %v", err)
		}

		if err := manager.setTagsOnNewDevices(groupName, oldGroupConfig.Devices, devices, tag); err != nil {
			log.Printf("Ошибка установки тегов на новые устройства: %v", err)
		}
	}

	settings.mu.Lock()
	settings.Groups[groupName] = GroupConfig{
		Devices:       devices,
		Tag:           tag,
		Schedule:      oldGroupConfig.Schedule,
		DisableAction: oldGroupConfig.DisableAction,
		Leasetime:     oldGroupConfig.Leasetime,
	}
	settings.mu.Unlock()

	if err := saveSettings(); err != nil {
		response := Response{Desc: fmt.Sprintf("Ошибка сохранения: %v", err), Level: "error"}
		json.NewEncoder(w).Encode(response)
	} else {
		response := Response{Desc: fmt.Sprintf("Группа '%s' обновлена", groupName), Level: "success"}
		json.NewEncoder(w).Encode(response)
	}
}

func updateTagHandler(w http.ResponseWriter, r *http.Request) {
	if err := r.ParseMultipartForm(maxFormMemory); err != nil {
		if err := r.ParseForm(); err != nil {
			response := Response{Desc: fmt.Sprintf("Ошибка парсинга формы: %v", err), Level: "error"}
			json.NewEncoder(w).Encode(response)
			return
		}
	}

	tagName := r.FormValue("tagname")
	dhcpOptionsStr := strings.TrimSpace(r.FormValue("dhcpoptions"))

	if tagName == "" || dhcpOptionsStr == "" {
		response := Response{Desc: "Заполните все поля", Level: "error"}
		json.NewEncoder(w).Encode(response)
		return
	}

	settings.mu.RLock()
	_, exists := settings.Tags[tagName]
	settings.mu.RUnlock()

	if !exists {
		response := Response{Desc: fmt.Sprintf("Тег '%s' не найден", tagName), Level: "error"}
		json.NewEncoder(w).Encode(response)
		return
	}

	var options []string
	for _, line := range strings.Split(dhcpOptionsStr, "\n") {
		opt := strings.TrimSpace(line)
		if opt != "" {
			options = append(options, opt)
		}
	}

	if len(options) == 0 {
		response := Response{Desc: "Добавьте хотя бы одну DHCP опцию", Level: "error"}
		json.NewEncoder(w).Encode(response)
		return
	}

	if err := manager.deleteTag(tagName); err != nil {
		log.Printf("Ошибка удаления старого тега: %v", err)
	}

	if err := manager.createTag(tagName, options); err != nil {
		response := Response{Desc: fmt.Sprintf("Ошибка обновления тега: %v", err), Level: "error"}
		json.NewEncoder(w).Encode(response)
	} else {
		settings.mu.Lock()
		settings.Tags[tagName] = TagConfig{DHCPOptions: options}
		settings.mu.Unlock()

		if err := saveSettings(); err != nil {
			response := Response{Desc: fmt.Sprintf("Ошибка сохранения: %v", err), Level: "error"}
			json.NewEncoder(w).Encode(response)
		} else {
			response := Response{Desc: fmt.Sprintf("Тег '%s' обновлён", tagName), Level: "success"}
			json.NewEncoder(w).Encode(response)
		}
	}
}

func deleteGroupHandler(w http.ResponseWriter, r *http.Request) {
	groupName := r.FormValue("group_name")

	settings.mu.RLock()
	_, exists := settings.Groups[groupName]
	settings.mu.RUnlock()

	if !exists {
		response := Response{Desc: fmt.Sprintf("Группа %s не найдена", groupName), Level: "error"}
		json.NewEncoder(w).Encode(response)
		return
	}

	settings.mu.Lock()
	delete(settings.Groups, groupName)
	settings.mu.Unlock()

	if err := saveSettings(); err != nil {
		response := Response{Desc: fmt.Sprintf("Ошибка сохранения: %v", err), Level: "error"}
		json.NewEncoder(w).Encode(response)
	} else {
		response := Response{Desc: fmt.Sprintf("Группа %s удалена", groupName), Level: "success"}
		json.NewEncoder(w).Encode(response)
	}
}

func saveFilterHandler(w http.ResponseWriter, r *http.Request) {
	filterContent := r.FormValue("filter_content")

	if err := saveFilterList(filterContent); err != nil {
		response := Response{Desc: fmt.Sprintf("Ошибка сохранения: %v", err), Level: "error"}
		json.NewEncoder(w).Encode(response)
	} else {
		// Обновляем фильтры в AdGuard Home
		if err := refreshAdGuardFilters(); err != nil {
			log.Printf("Warning: Failed to refresh AdGuard filters: %v", err)
			// Файл сохранен, но AdGuard не обновлен - показываем предупреждение
			response := Response{Desc: "Фильтр лист сохранён, но не удалось обновить AdGuard Home", Level: "warning"}
			json.NewEncoder(w).Encode(response)
		} else {
			response := Response{Desc: "Фильтр лист сохранён и обновлён в AdGuard Home", Level: "success"}
			json.NewEncoder(w).Encode(response)
		}
	}
}

func getPageData() PageData {
	settings.mu.RLock()
	settingsCopy := Settings{
		Groups:      make(map[string]GroupConfig),
		Tags:        make(map[string]TagConfig),
		SSHHost:     settings.SSHHost,
		SSHUser:     settings.SSHUser,
		SSHPass:     settings.SSHPass,
		AutoConnect: settings.AutoConnect,
		Password:    settings.Password,
		AdGuardHost: settings.AdGuardHost,
		AdGuardUser: settings.AdGuardUser,
		AdGuardPass: settings.AdGuardPass,
	}
	for k, v := range settings.Groups {
		settingsCopy.Groups[k] = v
	}
	for k, v := range settings.Tags {
		settingsCopy.Tags[k] = v
	}
	settings.mu.RUnlock()

	data := PageData{
		Connected:     manager.connected,
		Settings:      settingsCopy,
		GroupStates:   make(map[string]bool),
		HostStates:    make(map[string]string),
		ExistingHosts: []string{},
		FilterContent: loadFilterList(),
	}

	themeMutex.RLock()
	data.DarkTheme = darkTheme
	themeMutex.RUnlock()

	if manager.connected {
		groupStates, hostStates, _ := manager.getGroupStates()
		data.GroupStates = groupStates
		data.HostStates = hostStates

		existingHosts, _ := manager.getExistingHosts()
		data.ExistingHosts = existingHosts
	}

	return data
}

func filterFileHandler(w http.ResponseWriter, r *http.Request) {
	// Извлекаем имя файла из URL
	filename := strings.TrimPrefix(r.URL.Path, "/lists/")

	// Очищаем путь от path traversal
	filename = filepath.Clean(filename)

	// Проверяем на недопустимые символы
	if filename == "" || filename == "." || strings.HasPrefix(filename, ".") {
		http.Error(w, "Invalid filename", http.StatusBadRequest)
		return
	}

	// Ограничиваем только файлы .list
	if !strings.HasSuffix(filename, ".list") {
		http.Error(w, "Only .list files allowed", http.StatusForbidden)
		return
	}

	// Строим абсолютный путь к файлу
	filePath := filepath.Join(listsDir, filename)
	absFilePath, err := filepath.Abs(filePath)
	if err != nil {
		http.Error(w, "Invalid path", http.StatusBadRequest)
		return
	}

	// Проверяем, что файл находится внутри директории lists/
	absListsDir, err := filepath.Abs(listsDir)
	if err != nil {
		http.Error(w, "Internal server error", http.StatusInternalServerError)
		return
	}

	if !strings.HasPrefix(absFilePath, absListsDir+string(filepath.Separator)) {
		http.Error(w, "Access denied", http.StatusForbidden)
		return
	}

	// Проверяем, что файл существует и это обычный файл
	fileInfo, err := os.Stat(absFilePath)
	if os.IsNotExist(err) {
		http.Error(w, "File not found", http.StatusNotFound)
		return
	}
	if err != nil {
		http.Error(w, "Internal server error", http.StatusInternalServerError)
		return
	}
	if !fileInfo.Mode().IsRegular() {
		http.Error(w, "Invalid file type", http.StatusBadRequest)
		return
	}

	// Открываем файл
	file, err := os.Open(absFilePath)
	if err != nil {
		http.Error(w, "Internal server error", http.StatusInternalServerError)
		return
	}
	defer file.Close()

	// Устанавливаем заголовки безопасности и отдаем файл
	w.Header().Set("Cache-Control", "no-cache, no-store, must-revalidate")
	w.Header().Set("Pragma", "no-cache")
	w.Header().Set("Expires", "0")
	w.Header().Set("Content-Type", "text/plain; charset=utf-8")
	w.Header().Set("Content-Disposition", fmt.Sprintf("inline; filename=\"%s\"", filename))
	w.Header().Set("X-Content-Type-Options", "nosniff")

	http.ServeContent(w, r, filename, fileInfo.ModTime(), file)
}

func securityHeadersMiddleware(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("X-Content-Type-Options", "nosniff")
		w.Header().Set("X-Frame-Options", "DENY")
		w.Header().Set("X-XSS-Protection", "1; mode=block")
		w.Header().Set("Referrer-Policy", "strict-origin-when-cross-origin")

		csp := "default-src 'self'; " +
			"script-src 'self' 'unsafe-inline'; " +
			"style-src 'self' 'unsafe-inline'; " +
			"img-src 'self' data:; " +
			"font-src 'self'; " +
			"connect-src 'self'; " +
			"frame-ancestors 'none'"
		w.Header().Set("Content-Security-Policy", csp)

		if r.TLS != nil {
			w.Header().Set("Strict-Transport-Security", "max-age=31536000; includeSubDomains; preload")
		}

		next.ServeHTTP(w, r)
	})
}

/* ==================== MAIN ==================== */

func main() {
	initDirectories()
	initSettings()

	manager = NewOpenWrtManager()

	// Планировщик для автоматического управления группами
	go func() {
		for {
			if manager.connected {
				// Сначала применяем текущие расписания
				manager.checkAndApplySchedules()

				// Затем вычисляем когда следующая проверка
				nextCheck := manager.getNextScheduleTime()

				if nextCheck > 0 {
					select {
					case <-time.After(nextCheck):
						// Время пришло, продолжаем цикл
						// (checkAndApplySchedules вызовется в начале следующей итерации)
					case <-scheduleCheckTrigger:
						// Немедленная проверка по триггеру
						log.Println("Немедленная проверка расписания по триггеру")
					}
				} else {
					select {
					case <-time.After(scheduleNoConnectionInterval):
					case <-scheduleCheckTrigger:
						log.Println("Немедленная проверка расписания по триггеру")
					}
				}
			} else {
				time.Sleep(disconnectedCheckInterval)
			}
		}
	}()

	mux := http.NewServeMux()

	// Публичные endpoints
	mux.HandleFunc("/login", loginHandler)
	mux.HandleFunc("/logout", logoutHandler)
	mux.HandleFunc("/health", healthHandler)

	// Защищенные endpoints с редиректом
	mux.HandleFunc("/connect", connectHandler)
	mux.HandleFunc("/disconnect", disconnectHandler)

	// API endpoints с middleware
	mux.HandleFunc("/api/theme", apiPostMiddleware(themeHandler))
	mux.HandleFunc("/api/status", apiMiddleware(statusHandler))
	mux.HandleFunc("/api/schedule/", apiMiddleware(scheduleGetHandler))
	mux.HandleFunc("/api/schedule-save", apiPostMiddleware(scheduleSaveHandler))
	mux.HandleFunc("/api/schedule-toggle", apiPostMiddleware(scheduleToggleHandler))
	mux.HandleFunc("/api/disable-action/", apiMiddleware(disableActionGetHandler))
	mux.HandleFunc("/api/disable-action-save", apiPostMiddleware(disableActionSaveHandler))
	mux.HandleFunc("/api/leasetime/", apiMiddleware(leasetimeGetHandler))
	mux.HandleFunc("/api/leasetime-save", apiPostMiddleware(leasetimeSaveHandler))
	mux.HandleFunc("/api/adguard-settings", apiPostMiddleware(adguardSettingsHandler))
	mux.HandleFunc("/api/adguard-test", apiMiddleware(adguardTestHandler))
	mux.HandleFunc("/api/toggle", apiPostMiddleware(toggleHandler))
	mux.HandleFunc("/api/remove-device", apiPostMiddleware(removeDeviceFromGroupsHandler))
	mux.HandleFunc("/api/create-tag", apiPostMiddleware(createTagHandler))
	mux.HandleFunc("/api/update-tag", apiPostMiddleware(updateTagHandler))
	mux.HandleFunc("/api/delete-tag", apiPostMiddleware(deleteTagHandler))
	mux.HandleFunc("/api/create-group", apiPostMiddleware(createGroupHandler))
	mux.HandleFunc("/api/update-group", apiPostMiddleware(updateGroupHandler))
	mux.HandleFunc("/api/delete-group", apiPostMiddleware(deleteGroupHandler))
	mux.HandleFunc("/api/save-filter", apiPostMiddleware(saveFilterHandler))

	mux.HandleFunc("/lists/", filterFileHandler)

	mux.HandleFunc("/", func(w http.ResponseWriter, r *http.Request) {
		if !isAuthenticated(r) {
			loginHandler(w, r)
			return
		}

		data := getPageData()

		// Проверяем параметр редактирования группы
		if editGroup := r.URL.Query().Get("edit"); editGroup != "" {
			settings.mu.RLock()
			groupConfig, exists := settings.Groups[editGroup]
			settings.mu.RUnlock()

			if exists {
				data.EditingGroup = editGroup
				data.EditingData = groupConfig

				if manager.connected {
					existingHosts, err := manager.getExistingHosts()
					if err == nil {
						data.ExistingHosts = existingHosts
					}
				}
			}
		}

		// Проверяем параметр редактирования тега
		if editTag := r.URL.Query().Get("edittag"); editTag != "" {
			settings.mu.RLock()
			tagConfig, exists := settings.Tags[editTag]
			settings.mu.RUnlock()

			if exists {
				data.EditingTag = editTag
				data.EditingTagData = tagConfig
			}
		}

		tmpl := template.Must(template.New("main").Parse(htmlTemplate))
		if err := tmpl.Execute(w, data); err != nil {
			log.Printf("Template execution error: %v", err)
			http.Error(w, "Internal server error", http.StatusInternalServerError)
		}
	})

	secureHandler := securityHeadersMiddleware(mux)

	port := os.Getenv("PORT")
	if port == "" {
		port = defaultPort
	}

	srv := &http.Server{
		Addr:              ":" + port,
		Handler:           secureHandler,
		ReadTimeout:       serverReadTimeout,
		WriteTimeout:      serverWriteTimeout,
		IdleTimeout:       serverIdleTimeout,
		ReadHeaderTimeout: serverReadHeaderTimeout,
		MaxHeaderBytes:    maxHeaderBytes,
	}

	// Graceful shutdown
	quit := make(chan os.Signal, channelBufferSize)
	signal.Notify(quit, syscall.SIGINT, syscall.SIGTERM)

	go func() {
		<-quit
		addLog("Shutting down server...", "info")

		ctx, cancel := context.WithTimeout(context.Background(), shutdownTimeout)
		defer cancel()

		if manager.connected {
			manager.mu.Lock()
			manager.disconnect()
			manager.mu.Unlock()
			addLog("SSH connection closed", "info")
		}

		if err := srv.Shutdown(ctx); err != nil {
			log.Fatalf("Server forced to shutdown: %v", err)
		}

		addLog("Server stopped gracefully", "info")
		os.Exit(0)
	}()

	useHTTPS := os.Getenv("USE_HTTPS")
	certFile := os.Getenv("HTTPS_CERT_FILE")
	keyFile := os.Getenv("HTTPS_KEY_FILE")

	if useHTTPS == "1" && certFile != "" && keyFile != "" {
		fmt.Printf("DNS Filter Manager запущен с HTTPS на порту %s!\n", port)
		fmt.Printf("Адрес: https://localhost:%s\n", port)
		log.Fatal(srv.ListenAndServeTLS(certFile, keyFile))
	} else {
		fmt.Printf("DNS Filter Manager запущен на порту %s!\n", port)
		fmt.Printf("Адрес: http://localhost:%s\n", port)
		log.Fatal(srv.ListenAndServe())
	}
}

const htmlTemplate = `
<!DOCTYPE html>
<html lang="ru" data-theme="{{if .DarkTheme}}dark{{else}}light{{end}}">
<head>
	<meta charset="UTF-8">
	<meta name="viewport" content="width=device-width, initial-scale=1.0">
	<title>DNS Filter Manager</title>
	<style>
		:root {
			--bg-color: #f8fafc;
			--card-bg: white;
			--text-color: #1e293b;
			--text-secondary: #64748b;
			--border-color: #e2e8f0;
			--shadow-color: rgba(0,0,0,0.1);
			--hover-bg: #f1f5f9;
			--primary-color: #3b82f6;
			--success-color: #10b981;
			--danger-color: #ef4444;
			--warning-color: #f59e0b;
			--toggle-bg: #cbd5e1;
			--toggle-active: #60a5fa;
		}

		[data-theme="dark"] {
			--bg-color: #0f172a;
			--card-bg: #1e293b;
			--text-color: #f1f5f9;
			--text-secondary: #94a3b8;
			--border-color: #51698b;
			--shadow-color: rgba(0,0,0,0.3);
			--hover-bg: #374151;
			--primary-color: #60a5fa;
			--success-color: #34d399;
			--danger-color: #f87171;
			--warning-color: #fbbf24;
			--toggle-bg: #475569;
			--toggle-active: #60a5fa;
		}

		* {
			margin: 0;
			padding: 0;
			box-sizing: border-box;
		}

		body {
			font-family: 'Inter', -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
			background: var(--bg-color);
			color: var(--text-color);
			line-height: 1.6;
			transition: all 0.3s ease;
			padding-top: 90px;
		}

		.container {
			max-width: 1200px;
			margin: 0 auto;
			padding: 20px;
		}

		.header {
			text-align: center;
			margin-bottom: 40px;
			display: {{if .Connected}}none{{else}}block{{end}};
		}

		.header h1 {
			font-size: 2.5rem;
			font-weight: 700;
			color: var(--text-color);
			margin-bottom: 8px;
		}

		.header p {
			color: var(--text-secondary);
			font-size: 1.1rem;
		}

		.controls-bar {
			position: fixed;
			top: 20px;
			right: 20px;
			display: flex;
			align-items: center;
			gap: 16px;
			background: var(--card-bg);
			padding: 12px 20px;
			border-radius: 12px;
			border: 1px solid var(--border-color);
			box-shadow: 0 4px 16px var(--shadow-color);
			z-index: 100;
			flex-wrap: wrap;
		}

		.connection-info {
			display: flex;
			align-items: center;
			gap: 8px;
			font-size: 14px;
		}

		.status-dot {
			width: 8px;
			height: 8px;
			border-radius: 50%;
			background: var(--danger-color);
		}

		.status-dot.connected {
			background: var(--success-color);
		}

		.theme-toggle-container {
			display: flex;
			align-items: center;
			gap: 8px;
		}

		.theme-toggle {
			position: relative;
			display: inline-block;
			width: 60px;
			height: 28px;
		}

		.theme-toggle input {
			opacity: 0;
			width: 0;
			height: 0;
		}

		.theme-slider {
			position: absolute;
			cursor: pointer;
			top: 0;
			left: 0;
			right: 0;
			bottom: 0;
			background: var(--toggle-bg);
			border-radius: 34px;
			transition: 0.3s;
		}

		.theme-slider:before {
			position: absolute;
			content: "";
			height: 20px;
			width: 20px;
			left: 4px;
			bottom: 4px;
			background-color: white;
			border-radius: 50%;
			transition: 0.3s;
			background-repeat: no-repeat;
			background-position: center;
			background-size: 12px 12px;
			background-image: url('data:image/svg+xml;utf8,<svg viewBox="0 0 24 24" xmlns="http://www.w3.org/2000/svg"><path d="M12 3V5M12 19V21M5 12H3M21 12H19M17.8 6.2L16.4 7.6M7.6 16.4L6.2 17.8M17.8 17.8L16.4 16.4M7.6 7.6L6.2 6.2" stroke="%23999" stroke-width="2" stroke-linecap="round"/><circle cx="12" cy="12" r="4.5" fill="%23999" stroke="%23999" stroke-width="1"/></svg>');
		}

		input:checked + .theme-slider {
			background: var(--toggle-active);
		}

		input:checked + .theme-slider:before {
			transform: translateX(32px);
			background-image: url('data:image/svg+xml;utf8,<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24" fill="%234a90e2"><path d="M12 3a9 9 0 109 9c0-.46-.04-.92-.1-1.36a5.389 5.389 0 01-4.4 2.26 5.403 5.403 0 01-3.14-9.8c-.44-.06-.9-.1-1.36-.1z"/></svg>');
		}

		.schedule-modal {
			display: none;
			position: fixed;
			z-index: 1000;
			left: 0;
			top: 0;
			width: 100%;
			height: 100%;
			background-color: rgba(0,0,0,0.5);
			backdrop-filter: blur(4px);
			animation: fadeIn 0.2s ease;
		}

		@keyframes fadeIn {
			from { opacity: 0; }
			to { opacity: 1; }
		}

		.schedule-modal-content {
			background-color: var(--card-bg);
			margin: 10% auto;
			padding: 24px;
			border: 1px solid var(--border-color);
			border-radius: 12px;
			width: 450px;
			max-width: 90%;
			box-shadow: 0 4px 20px var(--shadow-color);
			animation: slideDown 0.3s ease;
		}

		@keyframes slideDown {
			from {
				opacity: 0;
				transform: translateY(-20px);
			}
			to {
				opacity: 1;
				transform: translateY(0);
			}
		}

		.time-inputs {
			display: grid;
			grid-template-columns: 1fr auto 1fr;
			gap: 12px;
			align-items: center;
			margin: 16px 0;
		}

		.time-group {
			display: flex;
			align-items: center;
			gap: 8px;
		}

		.time-select {
			width: 60px;
			padding: 8px;
			border: 1px solid var(--border-color);
			border-radius: 6px;
			background: var(--card-bg);
			color: var(--text-color);
		}

		.modal-actions {
			display: flex;
			gap: 12px;
			justify-content: flex-end;
			margin-top: 20px;
		}

		.schedule-controls {
			margin-top: 8px;
			padding-top: 8px;
			border-top: 1px solid var(--border-color);
		}

		.schedule-status {
			display: flex;
			align-items: center;
			gap: 12px;
			font-size: 13px;
			margin-bottom: 6px;
		}

		.schedule-toggle-label {
			display: flex;
			align-items: center;
			gap: 6px;
			cursor: pointer;
		}

		.schedule-toggle-label input {
			width: auto;
			margin-right: 6px;
		}

		.card {
			background: var(--card-bg);
			border-radius: 12px;
			padding: 24px;
			margin-bottom: 24px;
			box-shadow: 0 1px 3px var(--shadow-color);
			border: 1px solid var(--border-color);
		}

		.card h3 {
			font-size: 1.25rem;
			font-weight: 600;
			color: var(--text-color);
			margin-bottom: 20px;
			padding-bottom: 12px;
			border-bottom: 2px solid var(--border-color);
		}

		.form-group {
			margin-bottom: 20px;
		}

		.form-group label {
			display: block;
			font-weight: 500;
			color: var(--text-color);
			margin-bottom: 6px;
		}

		.form-help {
			font-size: 12px;
			color: var(--text-secondary);
			margin-top: 4px;
		}

		input, select, textarea {
			width: 100%;
			padding: 12px 16px;
			border: 1px solid var(--border-color);
			border-radius: 8px;
			font-size: 14px;
			transition: all 0.2s ease;
			background: var(--card-bg);
			color: var(--text-color);
		}

		input:focus, select:focus, textarea:focus {
			outline: none;
			border-color: var(--primary-color);
			box-shadow: 0 0 0 3px rgba(59, 130, 246, 0.1);
		}

		.btn {
			display: inline-flex;
			align-items: center;
			justify-content: center;
			padding: 10px 20px;
			margin: 0;
			border: none;
			border-radius: 8px;
			font-size: 14px;
			font-weight: 500;
			cursor: pointer;
			transition: all 0.2s ease;
			text-decoration: none;
			gap: 8px;
			min-width: fit-content;
			white-space: nowrap;
			box-sizing: border-box;
		}

		.btn-primary {
			background: var(--primary-color);
			color: white;
		}

		.btn-primary:hover {
			filter: brightness(0.9);
		}

		.btn-secondary {
			background: var(--text-secondary);
			color: white;
		}

		.btn-secondary:hover {
			filter: brightness(0.9);
		}

		.btn-success {
			background: var(--success-color);
			color: white;
		}

		.btn-success:hover {
			filter: brightness(0.9);
		}

		.btn-danger {
			background: var(--danger-color);
			color: white;
		}

		.btn-danger:hover {
			filter: brightness(0.9);
		}

		.btn-small {
			padding: 8px 16px;
			font-size: 12px;
			min-width: 80px;
			justify-content: center;
			height: 32px;
			line-height: 1;
		}

		.grid {
			display: grid;
			gap: 20px;
		}

		.grid-cols-2 {
			grid-template-columns: 1fr 1fr;
		}

		.toggle-switch {
			position: relative;
			display: inline-block;
			width: 60px;
			height: 34px;
		}

		.toggle-switch input {
			opacity: 0;
			width: 0;
			height: 0;
		}

		.slider {
			position: absolute;
			cursor: pointer;
			top: 0;
			left: 0;
			right: 0;
			bottom: 0;
			background: var(--toggle-bg);
			transition: .3s;
			border-radius: 34px;
		}

		.slider:before {
			position: absolute;
			content: "";
			height: 26px;
			width: 26px;
			left: 4px;
			bottom: 4px;
			background-color: white;
			transition: .3s;
			border-radius: 50%;
			box-shadow: 0 2px 4px rgba(0,0,0,0.2);
		}

		input:checked + .slider {
			background: var(--toggle-active);
		}

		input:checked + .slider:before {
			transform: translateX(26px);
		}

		.group-item {
			display: flex;
			justify-content: space-between;
			align-items: flex-start;
			padding: 16px;
			background: var(--hover-bg);
			border-radius: 8px;
			margin-bottom: 12px;
			border: 1px solid var(--border-color);
			flex-wrap: wrap;
			gap: 12px;
		}

		.group-item.active {
			background: rgba(239, 68, 68, 0.02);
			border-color: var(--danger-color);
		}

		.group-content {
			flex: 1;
			min-width: 300px;
		}

		.group-actions {
			display: flex;
			align-items: center;
			gap: 12px;
			flex-shrink: 0;
		}

		.device-list {
			font-size: 13px;
			color: var(--text-secondary);
			margin-top: 4px;
			display: flex;
			flex-wrap: wrap;
			gap: 6px;
		}

		.device-list code {
			background: rgba(59, 130, 246, 0.1);
			padding: 2px 6px;
			border-radius: 4px;
			font-family: 'Monaco', monospace;
			font-size: 12px;
			color: var(--primary-color);
			white-space: nowrap;
		}

		.status-badge {
			padding: 2px 8px;
			border: 1px solid var(--border-color);
			border-radius: 12px;
			font-size: 11px;
			font-weight: 500;
		}

		.status-active {
			color: var(--success-color);
		}

		.status-inactive {
			color: var(--warning-color);
		}

		.status-missing {
			color: var(--danger-color);
		}

		.btn-remove-device {
			display: inline-flex;
			align-items: center;
			justify-content: center;
			width: 16px;
			height: 16px;
			margin-left: 4px;
			border: none;
			border-radius: 50%;
			background: var(--danger-color);
			color: white;
			font-size: 10px;
			font-weight: bold;
			line-height: 1;
			cursor: pointer;
			transition: all 0.2s ease;
			padding: 0;
			vertical-align: middle;
			position: relative;
			top: -1px;
		}

		.btn-remove-device:hover {
			background: #dc2626;
		}

		.device-selector {
			border: 1px solid var(--border-color);
			border-radius: 8px;
			background: var(--card-bg);
			overflow: hidden;
		}

		.device-selector summary {
			padding: 12px 16px;
			cursor: pointer;
			user-select: none;
			font-weight: 500;
			background: var(--hover-bg);
			margin: 0;
			display: flex;
			justify-content: space-between;
			align-items: center;
		}

		.device-selector summary::-webkit-details-marker {
			display: none;
		}

		.device-selector summary::after {
			content: '▼';
			transition: transform 0.3s ease;
			font-size: 12px;
			color: var(--text-secondary);
		}

		.device-selector[open] summary {
			border-bottom: 1px solid var(--border-color);
		}

		.device-selector[open] summary::after {
			transform: rotate(180deg);
		}

		.device-options {
			padding: 16px;
			max-height: 200px;
			overflow-y: auto;
			background: var(--card-bg);
		}

		.device-checkbox {
			display: block;
			margin: 8px 0;
			cursor: pointer;
			padding: 4px 0;
		}

		.device-checkbox input {
			width: auto;
			margin-right: 8px;
		}

		.status-message {
			position: fixed;
			top: 20px;
			right: 20px;
			max-width: 350px;
			padding: 16px;
			border-radius: 8px;
			color: #333;
			font-weight: 500;
			font-size: 14px;
			z-index: 1000;
			transform: translateY(-120%);
			transition: transform 0.4s cubic-bezier(0.68, -0.55, 0.265, 1.55);
			border: 1px solid;
			word-wrap: break-word;
			box-shadow: 0 4px 20px rgba(0,0,0,0.15);
			display: flex;
			align-items: center;
			gap: 12px;
		}

		.status-message::before {
			content: '';
			font-size: 18px;
			flex-shrink: 0;
		}

		.status-message.success {
			background: linear-gradient(135deg, #e8f5e8 0%, #d4f6d4 100%);
			border-color: #4caf50;
		}

		.status-message.success::before {
			content: '✅';
		}

		.status-message.error {
			background: linear-gradient(135deg, #ffeaea 0%, #ffcccb 100%);
			border-color: #f44336;
		}

		.status-message.error::before {
			content: '❌';
		}

		.status-message.warning {
			background: linear-gradient(135deg, #fff8e1 0%, #ffecb3 100%);
			border-color: #ff9800;
			color: #e65100;
		}

		.status-message.warning::before {
			content: '⚠️';
		}

		.status-message.info {
			background: linear-gradient(135deg, #e3f2fd 0%, #bbdefb 100%);
			border-color: #2196f3;
			color: #1976d2;
		}

		.status-message.info::before {
			content: 'ℹ️';
		}

		.status-message.show {
			transform: translateY(0);
		}

		#connection-indicator {
			position: fixed;
			top: 20px;
			left: 50%;
			transform: translateX(-50%);
			background: var(--card-bg);
			padding: 12px 24px;
			border-radius: 12px;
			border: 1px solid var(--border-color);
			box-shadow: 0 4px 16px var(--shadow-color);
			z-index: 999;
			font-size: 14px;
			color: var(--text-color);
			display: flex;
			align-items: center;
			gap: 12px;
		}

		#connection-indicator::before {
			content: '';
			width: 16px;
			height: 16px;
			min-width: 16px;
			min-height: 16px;
			flex-shrink: 0;
			border: 2px solid var(--primary-color);
			border-top-color: transparent;
			border-radius: 50%;
			animation: spin 1s linear infinite;
		}

		@keyframes spin {
			to { transform: rotate(360deg); }
		}

		.connection-form {
			display: grid;
			grid-template-columns: 1fr 1fr 1fr auto;
			gap: 12px;
			align-items: end;
			margin-top: 12px;
		}

		.connection-form input {
			padding: 8px 12px;
			font-size: 14px;
		}

		.connection-form .btn-primary {
			height: 35px;
			padding: 0 20px;
		}

		.action-buttons {
			display: flex;
			gap: 8px;
			align-items: center;
			flex-wrap: wrap;
		}

		.action-buttons .btn-small {
			width: 80px;
			height: 32px;
			padding: 0;
			display: flex;
			align-items: center;
			justify-content: center;
			flex-shrink: 0;
		}

		@media (max-width: 1024px) {
			body {
				padding-top: 0px;
			}

			.controls-bar {
				position: static;
				justify-content: center;
				margin-bottom: 20px;
				gap: 12px;
				border-radius: 0;
				top: 0;
				right: 0;
				left: 0;
				max-width: none;
			}

			.header h1 {
				font-size: 2rem;
			}
		}

		@media (max-width: 768px) {
			body {
				padding-top: 0px;
			}

			.container {
				padding: 16px;
			}

			.connection-form {
				grid-template-columns: 1fr;
			}

			.card {
				padding: 16px;
			}

			.header h1 {
				font-size: 1.8rem;
			}

			.status-message {
				max-width: calc(100vw - 40px);
				right: 20px;
				left: 20px;
			}

			.controls-bar {
				margin-bottom: 10px;
				padding: 8px 16px;
				border-radius: 0;
			}

			.connection-info {
				font-size: 13px;
			}

			.group-item {
				flex-direction: column;
				align-items: stretch;
			}

			.group-actions {
				justify-content: flex-end;
			}

			.card form .action-buttons {
				width: 100%;
				flex-direction: column;
			}

			.card form .action-buttons .btn {
				width: 100%;
				flex: 1 1 100%;
			}

			.schedule-modal-content {
				width: calc(100vw - 40px);
				margin: 5% auto;
			}

			.schedule-toggle-label {
				position: relative;
				padding: 12px;
				min-width: 48px;
				min-height: 48px;
				display: inline-flex;
				align-items: center;
				justify-content: center;
			}

			.schedule-toggle-label input[type="checkbox"] {
				transform: scale(1.5);
			}
		}

		@media (max-width: 480px) {
			.container {
				padding: 12px;
			}

			.card {
				padding: 12px;
			}

			.group-item {
				align-items: flex-start;
				gap: 12px;
			}

			.action-buttons {
				align-self: flex-end;
			}

			.device-options {
				max-height: 150px;
			}
		}
	</style>
</head>
<body>
	<div class="controls-bar">
		<div class="connection-info">
			{{if .Connected}}
			<span class="status-dot connected"></span>
			<span>Подключен к роутеру</span>
			<button onclick="location.href='/disconnect'" class="btn btn-secondary btn-small">Отключиться</button>
			{{else}}
			<span class="status-dot"></span>
			<span>Не подключен к роутеру</span>
			<button onclick="location.href='/logout'" class="btn btn-secondary btn-small">Выйти</button>
			{{end}}
		</div>

		<div class="theme-toggle-container">
			<span style="font-size: 12px; color: var(--text-secondary);">Тема:</span>
			<label class="theme-toggle">
				<input type="checkbox" id="theme-toggle" {{if .DarkTheme}}checked{{end}}>
				<span class="theme-slider"></span>
			</label>
		</div>
	</div>

	<div class="container">
		<div class="header">
			<h1>DNS Filter Manager</h1>
			<p>Управление DNS фильтрацией для устройств OpenWrt</p>
		</div>

		{{if not .Connected}}
		<!-- Connection Form -->
		<div class="card">
			<h3>Подключение к роутеру</h3>
			<form method="POST" action="/connect" class="connection-form">
				<input type="text" name="host" value="192.168.1.1:22" placeholder="Хост" required>
				<input type="text" name="user" value="root" placeholder="Пользователь" required>
				<input type="password" name="password" placeholder="Пароль" required>
				<button type="submit" class="btn btn-primary">Подключиться</button>

				<div style="grid-column: 1 / -1; margin-top: 5px;">
					<label style="display: flex; align-items: center; gap: 8px; cursor: pointer;">
						<input type="checkbox" name="auto_connect" {{if .Settings.AutoConnect}}checked{{end}} style="width: auto; margin-right: 4px;">
						<span>Автоматически подключаться при входе</span>
					</label>
				</div>
			</form>
		</div>
		<!-- AdGuard Home Settings -->
		<div class="card">
			<h3>Настройки AdGuard Home</h3>
			<form id="adguardForm">
				<div class="form-group">
					<label>Адрес AdGuard Home</label>
					<input type="text" name="adguard_host" placeholder="http://192.168.1.1:3000" value="{{.Settings.AdGuardHost}}">
					<small class="form-help">Оставьте пустым, чтобы не использовать автообновление фильтров</small>
				</div>

				<div class="form-group">
					<label>Имя пользователя AdGuard</label>
					<input type="text" name="adguard_user" placeholder="admin" value="{{.Settings.AdGuardUser}}">
				</div>

				<div class="form-group">
					<label>Пароль AdGuard</label>
					<input type="password" name="adguard_pass" placeholder="Введите пароль для изменения">
				</div>

				<div class="action-buttons">
					<button type="button" onclick="saveAdGuardSettings()" class="btn btn-primary">Сохранить настройки</button>
					<button type="button" onclick="testAdGuardConnection()" class="btn btn-secondary">Проверить подключение</button>
				</div>
			</form>
		</div>
		{{else}}

		<!-- DNS Filtering Control -->
		<div class="card">
			<h3>Управление фильтрацией DNS</h3>

			{{if .Settings.Groups}}
			{{range $group, $config := .Settings.Groups}}
			<div class="group-item {{if index $.GroupStates $group}}active{{end}}">
				<div class="group-content">
					<div style="font-weight: 600; font-size: 16px;">{{$group}}</div>
					<div class="device-list">
						Устройства:
						{{range $i, $device := $config.Devices}}
						{{if $i}}, {{end}}<code>{{$device}}</code>
						<span class="status-badge">
						{{$status := index $.HostStates $device}}
						{{if eq $status $config.Tag}}<span class="status-active">{{$status}}</span>
						{{else if eq $status "no-tag"}}<span class="status-inactive">без фильтрации</span>
						{{else if eq $status "not-exists"}}
							<span class="status-missing">не найдено</span>
							<button class="btn-remove-device" onclick="removeDevice('{{$device}}')" title="Удалить устройство из всех групп">✕</button>
						{{else}}<span class="status-active">{{$status}}</span>{{end}}
						</span>
						{{end}}
					</div>

					<!-- Блок управления расписанием -->
					<div class="schedule-controls">
						{{$schedule := $config.Schedule}}
						{{if $schedule}}
						<div class="schedule-status">
							<label class="schedule-toggle-label" title="{{if $schedule.Enabled}}Выключить расписание{{else}}Включить расписание{{end}}">
								<input type="checkbox" {{if $schedule.Enabled}}checked{{end}}
									   onchange="toggleSchedule('{{$group}}', this.checked); updateScheduleTooltip(this)">
								Расписание
							</label>
							{{if $schedule.Enabled}}
							<span style="color: var(--text-secondary);">
								(отключение фильтра с {{printf "%02d:%02d" $schedule.StartHour $schedule.StartMin}}
								по {{printf "%02d:%02d" $schedule.EndHour $schedule.EndMin}})
							</span>
							{{else}}
							<span style="color: var(--text-secondary);">
								(ручное управление)
							</span>
							{{end}}
						</div>
						{{end}}
						<button type="button" class="btn btn-secondary btn-small"
								onclick="openScheduleModal('{{$group}}')"
								style="margin-top: 6px; font-size: 12px; padding: 4px 8px;">
							Настроить расписание
						</button>
						<button type="button" class="btn btn-secondary btn-small"
								onclick="openDisableActionModal('{{$group}}')"
								style="margin-top: 6px; font-size: 12px; padding: 4px 8px;">
							Действие при отключении
						</button>
						<button type="button" class="btn btn-secondary btn-small"
								onclick="openLeasetimeModal('{{$group}}')"
								style="margin-top: 6px; font-size: 12px; padding: 4px 8px;">
							TTL (срок аренды)
						</button>
					</div>
				</div>

				<div class="group-actions">
					<form method="POST" action="/api/toggle">
						<input type="hidden" name="group" value="{{$group}}">
						<label class="toggle-switch">
							<input type="checkbox" {{if index $.GroupStates $group}}checked{{end}} onchange="handleToggleChange(event, '{{$group}}')">
							<span class="slider"></span>
						</label>
					</form>
				</div>
			</div>
			{{end}}
			{{else}}
			<p style="color: var(--text-secondary); font-style: italic;">Группы не созданы. Создайте теги и группы ниже.</p>
			{{end}}
		</div>

		<!-- Tag Management -->
		<div class="card">
			<h3>Управление DNS-тегами</h3>

			{{if .EditingTag}}
			<!-- Edit Tag Form -->
			<form method="POST" action="/api/update-tag">
				<input type="hidden" name="tagname" value="{{.EditingTag}}">

				<div class="form-group">
					<label>Название тега</label>
					<input type="text" value="{{.EditingTag}}" disabled style="background: var(--hover-bg);">
					<div class="form-help">Название тега нельзя изменить</div>
				</div>

				<div class="form-group">
					<label>DHCP опции</label>
					<textarea name="dhcpoptions" rows="3" placeholder="6,192.168.1.5&#10;42,192.168.1.1&#10;3,192.168.1.1" required autofocus>{{range $i, $opt := .EditingTagData.DHCPOptions}}{{if $i}}&#10;{{end}}{{$opt}}{{end}}</textarea>
					<div class="form-help">Каждая опция на отдельной строке. Формат: код_опции,значение</div>
				</div>

				<div class="action-buttons">
					<button type="submit" class="btn btn-success">Сохранить</button>
					<button type="button" onclick="location.href='/'" class="btn btn-secondary">Отмена</button>
				</div>
			</form>
			{{else}}
			<!-- Create Tag Form -->
			<form method="POST" action="/api/create-tag" class="grid grid-cols-2">
				<div class="form-group">
					<label>Название тега</label>
					<input type="text" name="tagname" placeholder="filterdns" required>
					<div class="form-help">Уникальный идентификатор DNS-тега</div>
				</div>

				<div class="form-group">
					<label>DHCP опции</label>
					<textarea name="dhcpoptions" rows="3" placeholder="6,192.168.1.5&#10;42,192.168.1.1&#10;3,192.168.1.1" required></textarea>
					<div class="form-help">Каждая опция на отдельной строке. Формат: код_опции,значение</div>
				</div>

				<div class="form-group" style="grid-column: span 2;">
					<button type="submit" class="btn btn-success">Создать тег</button>
				</div>
			</form>

			<!-- Existing Tags -->
			{{if .Settings.Tags}}
			<div style="margin-top: 20px;">
				<strong>Существующие теги</strong>
				{{range $tag, $config := .Settings.Tags}}
				<div class="group-item">
					<div>
						<strong>{{$tag}}</strong>
						<div class="device-list">{{range $i, $opt := $config.DHCPOptions}}{{if $i}}, {{end}}<code>{{$opt}}</code>{{end}}</div>
					</div>
					<div class="action-buttons">
						<button onclick="editTag('{{$tag}}')" class="btn btn-primary btn-small">Изменить</button>
						<form method="POST" action="/api/delete-tag" style="display: inline;">
							<input type="hidden" name="tag_name" value="{{$tag}}">
							<button type="submit" class="btn btn-danger btn-small">Удалить</button>
						</form>
					</div>
				</div>
				{{end}}
			</div>
			{{end}}
			{{end}}
		</div>

		<!-- Group Management -->
		<div class="card">
			<h3>Управление группами</h3>

			{{if .EditingGroup}}
			<!-- Edit Form -->
			<form method="POST" action="/api/update-group">
				<input type="hidden" name="groupname" value="{{.EditingGroup}}">

				<div class="form-group">
					<label>Название группы</label>
					<input type="text" value="{{.EditingGroup}}" disabled style="background: var(--hover-bg);">
					<div class="form-help">Название группы нельзя изменить</div>
				</div>

				<div class="form-group">
					<label>Тег</label>
					<select name="tag" required autofocus>
						<option value="">Выберите тег</option>
						{{range $tag, $config := $.Settings.Tags}}
						<option value="{{$tag}}" {{if eq $tag $.EditingData.Tag}}selected{{end}}>{{$tag}}</option>
						{{end}}
					</select>
				</div>

				<div class="form-group">
					<label>Устройства</label>
					{{if .ExistingHosts}}
					<details class="device-selector" open>
						<summary>Выбрано: {{len .EditingData.Devices}}</summary>
						<div class="device-options">
							{{range $host := .ExistingHosts}}
							<label class="device-checkbox">
								{{$isChecked := false}}
								{{range $.EditingData.Devices}}
									{{if eq . $host}}
										{{$isChecked = true}}
									{{end}}
								{{end}}
								<input type="checkbox" name="devices" value="{{$host}}" {{if $isChecked}}checked{{end}}> {{$host}}
							</label>
							{{end}}
						</div>
					</details>
					{{else}}
					<div style="padding: 16px; background: rgba(239, 68, 68, 0.1); border: 1px solid var(--danger-color); border-radius: 8px; color: var(--danger-color);">
						<strong>Ошибка:</strong> Не удалось загрузить список устройств<br>
					</div>
					{{end}}
				</div>

				<div class="action-buttons">
					<button type="submit" class="btn btn-success">Сохранить</button>
					<button type="button" onclick="location.href='/'" class="btn btn-secondary">Отмена</button>
				</div>
			</form>
			{{else}}
			<!-- Create Form -->
			<form method="POST" action="/api/create-group">
				<div class="grid grid-cols-2">
					<div class="form-group">
						<label>Название группы</label>
						<input type="text" name="groupname" required>
					</div>

					<div class="form-group">
						<label>Тег</label>
						<select name="tag" required>
							<option value="">Выберите тег</option>
							{{range $tag, $config := .Settings.Tags}}
							<option value="{{$tag}}">{{$tag}}</option>
							{{end}}
						</select>
					</div>
				</div>

				<div class="form-group">
					<label>Устройства</label>
					<details class="device-selector">
						<summary>Выбрать устройства</summary>
						<div class="device-options">
							{{range .ExistingHosts}}
							<label class="device-checkbox">
								<input type="checkbox" name="devices" value="{{.}}"> {{.}}
							</label>
							{{end}}
						</div>
					</details>
				</div>

				<button type="submit" class="btn btn-success">Создать группу</button>
			</form>

			<!-- Existing Groups -->
			{{if .Settings.Groups}}
			<div style="margin-top: 30px;">
				<strong>Существующие группы</strong>
				{{range $group, $config := .Settings.Groups}}
				<div class="group-item">
					<div>
						<strong>{{$group}}</strong>
						<div class="device-list">
							{{$config.Tag}}: {{range $i, $device := $config.Devices}}{{if $i}}, {{end}}{{$device}}{{end}}
						</div>
					</div>
					<div class="action-buttons">
						<button onclick="editGroup('{{$group}}')" class="btn btn-primary btn-small">Изменить</button>
						<form method="POST" action="/api/delete-group" style="display: inline;">
							<input type="hidden" name="group_name" value="{{$group}}">
							<button type="submit" class="btn btn-danger btn-small">Удалить</button>
						</form>
					</div>
				</div>
				{{end}}
			</div>
			{{end}}
			{{end}}
		</div>

		<!-- Filter List Management -->
		<div class="card">
			<h3>Управление фильтр листом</h3>
			<form method="POST" action="/api/save-filter">
				<div class="form-group">
					<label>Список доменов для фильтрации</label>
					<textarea name="filter_content" rows="15" style="font-family: monospace;" placeholder="example.com">{{.FilterContent}}</textarea>
					<div class="form-help">Один домен на строку. При сохранении автоматически добавляются префикс "||" и постфикс "^" если они отсутствуют</div>
				</div>
				<button type="submit" class="btn btn-success">Сохранить фильтр лист</button>
			</form>

			{{if .FilterContent}}
			<div style="margin-top: 20px;">
				<strong>Ссылка на filter.list:</strong>
				<div style="margin-top: 8px;">
					<a href="/lists/filter.list" target="_blank" style="color: var(--primary-color); text-decoration: none; padding: 4px 8px; background: rgba(59, 130, 246, 0.1); border-radius: 4px; font-family: monospace; font-size: 13px;">filter.list</a>
				</div>
			</div>
			{{end}}
		</div>
		{{end}}
	</div>

	<!-- Модальное окно для настройки расписания -->
	<div id="scheduleModal" class="schedule-modal">
		<div class="schedule-modal-content">
			<h3>Настройка расписания для группы "<span id="scheduleGroupName"></span>"</h3>

			<form id="scheduleForm">
				<input type="hidden" id="modalGroupName" name="group_name">

				<div class="form-group">
					<label>
						<input type="checkbox" id="scheduleEnabled" name="enabled" value="true" style="width: auto; margin-right: 8px;">
						Включить автоматическое управление по расписанию
					</label>
				</div>

				<div class="form-group">
					<label>Время отключения фильтра:</label>
					<div class="time-inputs">
						<div class="time-group">
							<span>С</span>
							<select id="startHour" name="start_hour" class="time-select"></select>
							<span>:</span>
							<select id="startMin" name="start_min" class="time-select"></select>
						</div>

						<span>по</span>

						<div class="time-group">
							<select id="endHour" name="end_hour" class="time-select"></select>
							<span>:</span>
							<select id="endMin" name="end_min" class="time-select"></select>
						</div>
					</div>
					<div class="form-help">Фильтр будет автоматически отключаться в указанное время</div>
				</div>

				<div class="modal-actions">
					<button type="button" class="btn btn-secondary" onclick="closeScheduleModal()">Отмена</button>
					<button type="button" class="btn btn-success" onclick="saveSchedule()">Сохранить</button>
				</div>
			</form>
		</div>
	</div>

	<!-- Модальное окно для настройки действия при отключении -->
	<div id="disableActionModal" class="schedule-modal">
		<div class="schedule-modal-content">
			<h3 style="margin-bottom: 20px;">Действие при отключении фильтра</h3>
			<form id="disableActionForm">
				<input type="hidden" id="disableActionGroupName" name="group_name">

				<div class="form-group">
					<label style="display: flex; align-items: center; gap: 8px;">
						<input type="radio" name="mode" value="remove" checked onchange="toggleTagSelect()" style="width: auto; margin: 0;">
						<span>Удалять тег (устройство без фильтрации)</span>
					</label>
				</div>

				<div class="form-group">
					<label style="display: flex; align-items: center; gap: 8px;">
						<input type="radio" name="mode" value="switch" onchange="toggleTagSelect()" style="width: auto; margin: 0;">
						<span>Переключать на другой тег</span>
					</label>
				</div>

				<div class="form-group" id="alternativeTagGroup" style="display: none;">
					<label>Альтернативный тег</label>
					<select name="tag" id="alternativeTag">
						<option value="">Выберите тег</option>
						{{range $tag, $config := $.Settings.Tags}}
						<option value="{{$tag}}">{{$tag}}</option>
						{{end}}
					</select>
				</div>

				<div class="modal-actions">
					<button type="button" onclick="closeDisableActionModal()" class="btn btn-secondary">Отмена</button>
					<button type="button" onclick="saveDisableAction()" class="btn btn-primary">Сохранить</button>
				</div>
			</form>
		</div>
	</div>

	<!-- Модальное окно для настройки TTL -->
	<div id="leasetimeModal" class="schedule-modal">
		<div class="schedule-modal-content">
			<h3 style="margin-bottom: 20px;">Настройка срока аренды DHCP (TTL)</h3>
			<form id="leasetimeForm">
				<input type="hidden" id="leasetimeGroupName" name="group_name">

				<div class="form-group">
					<label style="display: flex; align-items: center; gap: 8px;">
						<input type="radio" name="mode" value="default" checked onchange="toggleLeasetimeInput()" style="width: auto; margin: 0;">
						<span>По умолчанию</span>
					</label>
				</div>

				<div class="form-group">
					<label style="display: flex; align-items: center; gap: 8px;">
						<input type="radio" name="mode" value="custom" onchange="toggleLeasetimeInput()" style="width: auto; margin: 0;">
						<span>Задать срок аренды</span>
					</label>
				</div>

				<div class="form-group" id="leasetimeInputGroup" style="display: none;">
					<label>Срок аренды</label>
					<div style="display: flex; align-items: center; gap: 12px;">
						<input type="number" name="leasetime" id="leasetimeValue" min="0" max="60" value="5" style="width: 100px;">
						<span>мин.</span>
					</div>
				</div>

				<div class="modal-actions">
					<button type="button" onclick="closeLeasetimeModal()" class="btn btn-secondary">Отмена</button>
					<button type="button" onclick="saveLeasetime()" class="btn btn-primary">Сохранить</button>
				</div>
			</form>
		</div>
	</div>

	<script>
		// Theme management
		function setTheme(isDark) {
			document.documentElement.setAttribute('data-theme', isDark ? 'dark' : 'light');
			localStorage.setItem('theme', isDark ? 'dark' : 'light');

			// Send theme to server
			fetch('/api/theme', {
				method: 'POST',
				headers: {'Content-Type': 'application/x-www-form-urlencoded'},
				body: 'theme=' + (isDark ? 'dark' : 'light')
			});
		}

		// Load saved theme
		function loadTheme() {
			const savedTheme = localStorage.getItem('theme');
			const systemDark = window.matchMedia('(prefers-color-scheme: dark)').matches;
			const isDark = savedTheme ? savedTheme === 'dark' : systemDark;

			document.getElementById('theme-toggle').checked = isDark;
			setTheme(isDark);
		}

		// Status message notifications
		function showStatus(message, type = 'success') {
			// Remove existing status message
			const existing = document.querySelector('.status-message');
			if (existing) existing.remove();

			// Create new status message
			const statusDiv = document.createElement('div');
			statusDiv.className = 'status-message ' + type;
			statusDiv.textContent = message;
			document.body.appendChild(statusDiv);

			// Show status message
			setTimeout(() => statusDiv.classList.add('show'), 100);

			// Auto hide
			setTimeout(() => {
				statusDiv.classList.remove('show');
				setTimeout(() => statusDiv.remove(), 300);
			}, 3000);
		}

		// Device count updater
		function updateDeviceCount() {
			document.addEventListener('change', function(e) {
				if (e.target.type === 'checkbox' && e.target.name === 'devices') {
					const container = e.target.closest('.device-selector');
					if (container) {
						const checkboxes = container.querySelectorAll('input[type="checkbox"]:checked');
						const summary = container.querySelector('summary');
						const count = checkboxes.length;
						if (summary.textContent.includes('выбрано')) {
							summary.textContent = summary.textContent.replace(/\d+ выбрано/, count + ' выбрано');
						} else {
							summary.textContent = 'Выберите устройства (' + count + ' выбрано)';
						}
					}
				}
			});
		}

		// Функции управления расписанием
		function openScheduleModal(groupName) {
			const modal = document.getElementById('scheduleModal');
			document.getElementById('modalGroupName').value = groupName;
			document.getElementById('scheduleGroupName').textContent = groupName;

			// Заполняем селекты времени
			populateTimeSelects();

			// Загружаем текущие данные расписания
			fetch('/api/schedule/' + groupName)
				.then(response => response.json())
				.then(data => {
					document.getElementById('scheduleEnabled').checked = data.enabled || false;
					document.getElementById('startHour').value = data.start_hour || 0;
					document.getElementById('startMin').value = data.start_min || 0;
					document.getElementById('endHour').value = data.end_hour || 23;
					document.getElementById('endMin').value = data.end_min || 0;
				})
				.catch(error => {
					console.error('Error loading schedule:', error);
				});

			modal.style.display = 'block';
		}

		function closeScheduleModal() {
			document.getElementById('scheduleModal').style.display = 'none';
		}

		function populateTimeSelects() {
			const hourSelects = ['startHour', 'endHour'];
			const minSelects = ['startMin', 'endMin'];

			hourSelects.forEach(id => {
				const select = document.getElementById(id);
				select.innerHTML = '';
				for(let i = 0; i < 24; i++) {
					select.innerHTML += '<option value="' + i + '">' + i.toString().padStart(2, '0') + '</option>';
				}
			});

			minSelects.forEach(id => {
				const select = document.getElementById(id);
				select.innerHTML = '';
				for(let i = 0; i < 60; i++) {
					select.innerHTML += '<option value="' + i + '">' + i.toString().padStart(2, '0') + '</option>';
				}
			});
		}

		function saveSchedule() {
			const formData = new FormData(document.getElementById('scheduleForm'));
			fetch('/api/schedule-save', {method: 'POST', body: formData})
				.then(response => response.json())
				.then(data => {
					if (data.level === 'success') {
						closeScheduleModal();
						showStatus('Расписание сохранено', 'success');
						setTimeout(() => location.reload(), 1000);
					} else {
						showStatus(data.desc, 'error');
					}
				})
				.catch(error => {
					console.error('Error saving schedule:', error);
					showStatus('Ошибка сохранения расписания', 'error');
				});
		}

		function toggleSchedule(groupName, enabled) {
			fetch('/api/schedule-toggle', {
				method: 'POST',
				headers: {'Content-Type': 'application/x-www-form-urlencoded'},
				body: 'group=' + encodeURIComponent(groupName) + '&enabled=' + enabled
			})
			.then(response => response.json())
			.then(data => {
				if (data.level === 'success') {
					showStatus(data.desc, 'success');
					setTimeout(() => location.reload(), 1000);
				} else {
					showStatus(data.desc, 'error');
				}
			})
			.catch(error => {
				console.error('Error toggling schedule:', error);
				showStatus('Ошибка переключения расписания', 'error');
			});
		}

		function updateScheduleTooltip(checkbox) {
			const label = checkbox.closest('label');
			if (checkbox.checked) {
				label.setAttribute('title', 'Выключить расписание');
			} else {
				label.setAttribute('title', 'Включить расписание');
			}
		}

		function removeDevice(deviceName) {
			if (!confirm('Удалить устройство "' + deviceName + '" из всех групп?\n\nЭто действие нельзя отменить.')) {
				return;
			}

			fetch('/api/remove-device', {
				method: 'POST',
				headers: {'Content-Type': 'application/x-www-form-urlencoded'},
				body: new URLSearchParams({device: deviceName})
			})
			.then(res => res.json())
			.then(data => {
				showStatus(data.desc, data.level);
				if (data.level === 'success') {
					setTimeout(() => location.reload(), 1000);
				}
			})
			.catch(err => {
				showStatus('Ошибка: ' + err.message, 'error');
			});
		}

		function openDisableActionModal(groupName) {
			document.getElementById('disableActionGroupName').value = groupName;

			// Загружаем текущие настройки
			fetch('/api/disable-action/' + groupName)
				.then(response => response.json())
				.then(data => {
					const modeRadios = document.getElementsByName('mode');
					modeRadios.forEach(radio => {
						radio.checked = radio.value === (data.mode || 'remove');
					});

					if (data.mode === 'switch' && data.tag) {
						document.getElementById('alternativeTag').value = data.tag;
					}

					toggleTagSelect();
				})
				.catch(error => {
					console.error('Error loading disable action:', error);
				});

			document.getElementById('disableActionModal').style.display = 'block';
		}

		function closeDisableActionModal() {
			document.getElementById('disableActionModal').style.display = 'none';
		}

		function toggleTagSelect() {
			const switchMode = document.querySelector('input[name="mode"][value="switch"]').checked;
			const tagGroup = document.getElementById('alternativeTagGroup');
			tagGroup.style.display = switchMode ? 'block' : 'none';

			if (!switchMode) {
				document.getElementById('alternativeTag').value = '';
			}
		}

		function saveDisableAction() {
			const formData = new FormData(document.getElementById('disableActionForm'));

			// Если выбран режим "remove", очищаем поле тега
			if (formData.get('mode') === 'remove') {
				formData.set('tag', '');
			}

			fetch('/api/disable-action-save', {method: 'POST', body: formData})
				.then(response => response.json())
				.then(data => {
					if (data.level === 'success') {
						closeDisableActionModal();
						showStatus('Настройки действия сохранены', 'success');
						setTimeout(() => location.reload(), 1000);
					} else {
						showStatus(data.desc, 'error');
					}
				})
				.catch(error => {
					console.error('Error saving disable action:', error);
					showStatus('Ошибка сохранения настроек', 'error');
				});
		}

		function openLeasetimeModal(groupName) {
			document.getElementById('leasetimeGroupName').value = groupName;

			// Сразу сбрасываем на дефолт (это предотвратит показ старых значений)
			const modeRadios = document.getElementsByName('mode');
			modeRadios.forEach(radio => {
				radio.checked = radio.value === 'default';
			});
			document.getElementById('leasetimeValue').value = 5;
			document.getElementById('leasetimeInputGroup').style.display = 'none';

			// Загружаем актуальные данные для конкретной группы
			fetch('/api/leasetime/' + encodeURIComponent(groupName))
				.then(response => response.json())
				.then(data => {
					// Применяем загруженные данные
					const modeRadios = document.getElementsByName('mode');
					modeRadios.forEach(radio => {
						radio.checked = radio.value === (data.mode || 'default');
					});

					if (data.mode === 'custom' && data.leasetime !== undefined) {
						document.getElementById('leasetimeValue').value = data.leasetime;
					}

					toggleLeasetimeInput();
				})
				.catch(error => {
					console.error('Error loading leasetime:', error);
					// При ошибке остаются дефолтные значения из ШАГа 1
				});

			// Показываем модальное окно
			document.getElementById('leasetimeModal').style.display = 'block';
		}

		function closeLeasetimeModal() {
			document.getElementById('leasetimeModal').style.display = 'none';

			// Сбрасываем форму при закрытии
			const modeRadios = document.getElementsByName('mode');
			modeRadios.forEach(radio => {
				radio.checked = radio.value === 'default';
			});
			document.getElementById('leasetimeValue').value = 5;
			document.getElementById('leasetimeInputGroup').style.display = 'none';
		}

		function toggleLeasetimeInput() {
			const customMode = document.querySelector('input[name="mode"][value="custom"]').checked;
			const inputGroup = document.getElementById('leasetimeInputGroup');
			inputGroup.style.display = customMode ? 'block' : 'none';
		}

		function saveLeasetime() {
			const formData = new FormData(document.getElementById('leasetimeForm'));

			// Если выбран режим "default", очищаем поле leasetime
			if (formData.get('mode') === 'default') {
				formData.set('leasetime', '0');
			}

			fetch('/api/leasetime-save', {method: 'POST', body: formData})
				.then(response => response.json())
				.then(data => {
					if (data.level === 'success') {
						closeLeasetimeModal();
						showStatus('Настройки срока аренды сохранены', 'success');
						setTimeout(() => location.reload(), 1000);
					} else {
						showStatus(data.desc, 'error');
					}
				})
				.catch(error => {
					console.error('Error saving leasetime:', error);
					showStatus('Ошибка сохранения настроек', 'error');
				});
		}

		function saveAdGuardSettings() {
			const form = document.getElementById('adguardForm');
			const formData = new FormData(form);

			fetch('/api/adguard-settings', {method: 'POST', body: formData})
				.then(response => response.json())
				.then(data => {
					showStatus(data.desc, data.level);
					if (data.level === 'success') {
						setTimeout(() => location.reload(), 1000);
					}
				})
				.catch(error => {
					console.error('Error saving AdGuard settings:', error);
					showStatus('Ошибка сохранения настроек', 'error');
				});
		}

		function testAdGuardConnection() {
			fetch('/api/adguard-test')
				.then(response => response.json())
				.then(data => {
					showStatus(data.desc, data.level);
				})
				.catch(error => {
					console.error('Error testing AdGuard connection:', error);
					showStatus('Ошибка проверки подключения', 'error');
				});
		}

		function handleToggleChange(event, groupName) {
			event.preventDefault();

			const checkbox = event.target;
			const form = checkbox.closest('form');
			const formData = new FormData(form);

			fetch('/api/toggle', {
				method: 'POST',
				body: formData
			})
			.then(response => response.json())
			.then(data => {
				if (data.level === 'success') {
					showStatus(data.desc, 'success');
					setTimeout(() => window.location.href = '/', 1000);
				} else {
					showStatus(data.desc, 'error');
					// Возвращаем чекбокс в предыдущее состояние при ошибке
					checkbox.checked = !checkbox.checked;
				}
			})
			.catch(error => {
				console.error('Error:', error);
				showStatus('Произошла ошибка при переключении группы', 'error');
				// Возвращаем чекбокс в предыдущее состояние при ошибке
				checkbox.checked = !checkbox.checked;
			});
		}

		// Обработчик для формы создания тега
		function handleTagFormSubmit(form, event) {
			event.preventDefault();

			const formData = new FormData(form);
			const action = form.getAttribute('action');

			fetch(action, {
				method: 'POST',
				body: formData
			})
			.then(response => response.json())
			.then(data => {
				if (data.level === 'success') {
					showStatus(data.desc, 'success');
					// Перенаправляем на главную страницу без параметров
					setTimeout(() => window.location.href = '/', 1000);
				} else {
					showStatus(data.desc, 'error');
				}
			})
			.catch(error => {
				console.error('Error:', error);
				showStatus('Произошла ошибка при сохранении тега', 'error');
			});
		}

		// Обработчик для формы создания группы
		function handleGroupFormSubmit(form, event) {
			event.preventDefault();

			const formData = new FormData(form);
			const action = form.getAttribute('action');

			fetch(action, {
				method: 'POST',
				body: formData
			})
			.then(response => response.json())
			.then(data => {
				if (data.level === 'success') {
					showStatus(data.desc, 'success');
					// Перенаправляем на главную страницу без параметров
					setTimeout(() => window.location.href = '/', 1000);
				} else {
					showStatus(data.desc, 'error');
				}
			})
			.catch(error => {
				console.error('Error:', error);
				showStatus('Произошла ошибка при сохранении группы', 'error');
			});
		}

		function editGroup(groupName) {
			// Создаем форму для редактирования
			const form = document.createElement('form');
			form.method = 'GET';
			form.action = '/';

			const input = document.createElement('input');
			input.type = 'hidden';
			input.name = 'edit';
			input.value = groupName;

			form.appendChild(input);
			document.body.appendChild(form);
			form.submit();
		}

		function editTag(tagName) {
			const form = document.createElement('form');
			form.method = 'GET';
			form.action = '/';

			const input = document.createElement('input');
			input.type = 'hidden';
			input.name = 'edittag';
			input.value = tagName;

			form.appendChild(input);
			document.body.appendChild(form);
			form.submit();
		}

		// Обработчик для формы фильтр листа
		function handleFilterFormSubmit(form, event) {
			event.preventDefault();

			const formData = new FormData(form);

			fetch('/api/save-filter', {
				method: 'POST',
				body: formData
			})
			.then(response => response.json())
			.then(data => {
				if (data.level === 'success') {
					showStatus(data.desc, 'success');
					// Перезагружаем страницу для обновления ссылки на файл
					setTimeout(() => location.reload(), 1000);
				} else {
					showStatus(data.desc, 'error');
				}
			})
			.catch(error => {
				console.error('Error:', error);
				showStatus('Произошла ошибка при сохранении фильтра', 'error');
			});
		}

		// Закрытие модальных окон по клику вне их
		window.onclick = function(event) {
			const scheduleModal = document.getElementById('scheduleModal');
			const disableActionModal = document.getElementById('disableActionModal');
			const leasetimeModal = document.getElementById('leasetimeModal');

			if (event.target === scheduleModal) {
				closeScheduleModal();
			}

			if (event.target === disableActionModal) {
				closeDisableActionModal();
			}

			if (event.target === leasetimeModal) {
				closeLeasetimeModal();
			}
		}

		// Обработчик для формы удаления тега
		function handleDeleteTagSubmit(form, event) {
			event.preventDefault();

			const formData = new FormData(form);
			const tagName = formData.get('tag_name');

			if (!confirm('Удалить тег ' + tagName + '?')) {
				return;
			}

			fetch('/api/delete-tag', {
				method: 'POST',
				body: formData
			})
			.then(response => response.json())
			.then(data => {
				if (data.level === 'success') {
					showStatus(data.desc, 'success');
					setTimeout(() => location.reload(), 1000);
				} else {
					showStatus(data.desc, 'error');
				}
			})
			.catch(error => {
				console.error('Error:', error);
				showStatus('Произошла ошибка при удалении тега', 'error');
			});
		}

		// Initialize
		document.addEventListener('DOMContentLoaded', function() {
			loadTheme();
			updateDeviceCount();

			// Theme toggle handler
			document.getElementById('theme-toggle').addEventListener('change', function() {
				setTheme(this.checked);
			});

			// System theme change listener
			window.matchMedia('(prefers-color-scheme: dark)').addEventListener('change', function() {
				if (!localStorage.getItem('theme')) {
					loadTheme();
				}
			});

			// Привязываем обработчики к формам создания тегов
			const tagForms = document.querySelectorAll('form[action="/api/create-tag"]');
			tagForms.forEach(form => {
				form.addEventListener('submit', function(event) {
					handleTagFormSubmit(this, event);
				});
			});

			// Привязываем обработчики к формам удаления тегов
			const deleteTagForms = document.querySelectorAll('form[action="/api/delete-tag"]');
			deleteTagForms.forEach(form => {
				form.addEventListener('submit', function(event) {
					handleDeleteTagSubmit(this, event);
				});
			});

			// Привязываем обработчики к формам удаления групп
			const deleteGroupForms = document.querySelectorAll('form[action="/api/delete-group"]');
			deleteGroupForms.forEach(form => {
				form.addEventListener('submit', function(event) {
					const groupName = this.querySelector('input[name="group_name"]').value;
					if (!confirm('Удалить группу ' + groupName + '?')) {
						event.preventDefault();
						return false;
					}

					event.preventDefault();
					const formData = new FormData(this);

					fetch('/api/delete-group', {
						method: 'POST',
						body: formData
					})
					.then(response => response.json())
					.then(data => {
						if (data.level === 'success') {
							showStatus(data.desc, 'success');
							setTimeout(() => location.reload(), 1000);
						} else {
							showStatus(data.desc, 'error');
						}
					})
					.catch(error => {
						console.error('Error:', error);
						showStatus('Произошла ошибка при удалении группы', 'error');
					});
				});
			});

			// Привязываем обработчики к формам создания групп
			const groupForms = document.querySelectorAll('form[action="/api/create-group"]');
			groupForms.forEach(form => {
				form.addEventListener('submit', function(event) {
					handleGroupFormSubmit(this, event);
				});
			});

			// Привязываем обработчики к формам редактирования групп
			const updateGroupForms = document.querySelectorAll('form[action="/api/update-group"]');
			updateGroupForms.forEach(form => {
				form.addEventListener('submit', function(event) {
					handleGroupFormSubmit(this, event);
				});
			});

			// Привязываем обработчики к формам редактирования тегов
			const updateTagForms = document.querySelectorAll('form[action="/api/update-tag"]');
			updateTagForms.forEach(form => {
				form.addEventListener('submit', function(event) {
					handleTagFormSubmit(this, event);
				});
			});

			// Привязываем обработчики к форме сохранения фильтра
			const filterForms = document.querySelectorAll('form[action="/api/save-filter"]');
			filterForms.forEach(form => {
				form.addEventListener('submit', function(event) {
					handleFilterFormSubmit(this, event);
				});
			});

			// Show messages
			{{if .Message}}showStatus('{{.Message}}', 'success');{{end}}
			{{if .Error}}showStatus('{{.Error}}', 'error');{{end}}
		});

		(function() {
			const urlParams = new URLSearchParams(window.location.search);
			const justLoggedIn = document.referrer.includes('/login') || urlParams.has('login');

			{{if not .Connected}}
			{{if .Settings.AutoConnect}}
			{{if .Settings.SSHHost}}
			// Проверяем, только что ли был вход
			if (justLoggedIn || sessionStorage.getItem('autoconnect_pending') === 'true') {
				sessionStorage.setItem('autoconnect_pending', 'true');

				let attempts = 0;
				const maxAttempts = 10; // 10 попыток × 500ms = 5 секунд

				function checkConnection() {
					attempts++;

					fetch('/api/status')
						.then(r => r.json())
						.then(data => {
							if (data.connected) {
								sessionStorage.removeItem('autoconnect_pending');
								location.reload();
							} else if (attempts < maxAttempts) {
								setTimeout(checkConnection, 500);
							} else {
								// Превышено время ожидания
								sessionStorage.removeItem('autoconnect_pending');
								console.log('SSH auto-connect timeout');
							}
						})
						.catch(err => {
							console.error('Connection check failed:', err);
							if (attempts < maxAttempts) {
								setTimeout(checkConnection, 500);
							}
						});
				}

				// Показываем индикатор подключения
				const indicator = document.createElement('div');
				indicator.id = 'connection-indicator';
				indicator.textContent = 'Подключение к роутеру...';
				document.body.appendChild(indicator);

				checkConnection();
			}
			{{end}}
			{{end}}
			{{end}}
		})();
	</script>
</body>
</html>
`
