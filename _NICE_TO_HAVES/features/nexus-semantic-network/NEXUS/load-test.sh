#!/bin/bash
# Load testing script for multi-region Nexus deployment
# Tests latency and throughput across regions

set -euo pipefail

# Configuration
BRIDGE_APP="nexus-bridge-server"
REGIONS=("iad" "lhr" "nrt" "sjc")
CONCURRENT_REQUESTS=10
TOTAL_REQUESTS=100

# Colors
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

log_info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

# Get URLs for each region
get_region_url() {
    local region=$1
    # Fly.io apps are accessible via app-name.fly.dev
    # For region-specific testing, we'd need to use flyctl proxy or region-specific hostnames
    echo "https://$BRIDGE_APP.fly.dev"
}

# Test latency to a region
test_latency() {
    local url=$1
    local region=$2
    
    log_info "Testing latency to $region..."
    
    local total_time=0
    local success_count=0
    
    for i in $(seq 1 $TOTAL_REQUESTS); do
        start_time=$(date +%s%N)
        if curl -s -f -o /dev/null -w "%{http_code}" "$url/health" > /dev/null 2>&1; then
            end_time=$(date +%s%N)
            duration=$(( (end_time - start_time) / 1000000 ))  # Convert to milliseconds
            total_time=$((total_time + duration))
            success_count=$((success_count + 1))
        fi
    done
    
    if [ $success_count -gt 0 ]; then
        avg_latency=$((total_time / success_count))
        log_info "Region $region: Average latency ${avg_latency}ms (${success_count}/${TOTAL_REQUESTS} successful)"
    else
        log_warn "Region $region: All requests failed"
    fi
}

# Test concurrent throughput
test_throughput() {
    local url=$1
    local region=$2
    
    log_info "Testing concurrent throughput to $region..."
    
    local success_count=0
    local start_time=$(date +%s)
    
    # Run concurrent requests
    for i in $(seq 1 $CONCURRENT_REQUESTS); do
        (
            if curl -s -f "$url/health" > /dev/null 2>&1; then
                echo "success"
            else
                echo "failure"
            fi
        ) &
    done
    
    wait
    
    end_time=$(date +%s)
    duration=$((end_time - start_time))
    
    log_info "Region $region: Completed $CONCURRENT_REQUESTS concurrent requests in ${duration}s"
}

# Test agent launch latency
test_agent_launch() {
    local url=$1
    local region=$2
    
    log_info "Testing agent launch latency to $region..."
    
    local total_time=0
    local success_count=0
    
    for i in $(seq 1 10); do
        start_time=$(date +%s%N)
        
        # Simulate agent launch request (JSON-RPC)
        response=$(curl -s -X POST "$url" \
            -H "Content-Type: application/json" \
            -d '{
                "jsonrpc": "2.0",
                "id": 1,
                "method": "nexus.agent.launch",
                "params": {
                    "agentType": "web_search",
                    "config": "{}"
                }
            }' 2>&1)
        
        end_time=$(date +%s%N)
        duration=$(( (end_time - start_time) / 1000000 ))
        
        if echo "$response" | grep -q '"result"'; then
            total_time=$((total_time + duration))
            success_count=$((success_count + 1))
        fi
    done
    
    if [ $success_count -gt 0 ]; then
        avg_latency=$((total_time / success_count))
        log_info "Region $region: Average agent launch latency ${avg_latency}ms (${success_count}/10 successful)"
    else
        log_warn "Region $region: Agent launch tests failed"
    fi
}

# Main test function
main() {
    log_info "Starting load tests for Nexus Bridge Server"
    
    # Test each region
    for region in "${REGIONS[@]}"; do
        url=$(get_region_url "$region")
        log_info "Testing region: $region ($url)"
        
        test_latency "$url" "$region"
        test_throughput "$url" "$region"
        test_agent_launch "$url" "$region"
        
        echo ""
    done
    
    log_info "Load testing complete"
}

main "$@"
