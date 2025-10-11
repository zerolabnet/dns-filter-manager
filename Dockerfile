FROM golang:1.25.1-alpine AS builder

WORKDIR /app

COPY go.mod go.sum ./
RUN go mod download

COPY . .

RUN CGO_ENABLED=0 GOOS=linux go build -ldflags="-s -w" -o dns-filter-manager main.go

FROM alpine:3.22

RUN addgroup -g 1000 appgroup && \
    adduser -u 1000 -G appgroup -D -s /bin/sh appuser

RUN apk --no-cache add ca-certificates tzdata && \
    rm -rf /var/cache/apk/*

RUN mkdir -p /app/lists && \
    chown -R appuser:appgroup /app

USER appuser
WORKDIR /app

ENV TZ=Europe/Moscow

COPY --from=builder --chown=appuser:appgroup /app/dns-filter-manager /app/

CMD ["./dns-filter-manager"]