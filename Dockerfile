# Use official lightweight Python image
FROM python:3.11-slim

# Prevent Python from writing .pyc files and enable unbuffered logging
ENV PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    PORT=8003 \
    HUENCY_THREADS=200 \
    HUENCY_CHANNELS=1000

# Install essential system dependencies and CA certificates for secure TLS requests
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    curl \
    && rm -rf /var/lib/apt/lists/*

# Set working directory
WORKDIR /app

# Install Python dependencies first for caching
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Copy application source code and configuration
COPY . .

# Expose default port (Railway automatically injects $PORT environment variable)
EXPOSE 8003

# Health check to ensure service responsiveness
HEALTHCHECK --interval=30s --timeout=5s --start-period=10s --retries=3 \
    CMD curl -f http://localhost:${PORT:-8003}/health || exit 1

# Start the application with waitress via main.py
CMD ["python", "main.py"]
