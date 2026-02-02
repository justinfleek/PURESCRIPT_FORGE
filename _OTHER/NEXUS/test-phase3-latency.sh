#!/bin/bash
# | Phase 3 Latency Measurement Script
# | Measures latency improvements for edge-native agent execution

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Configuration
FLY_API_TOKEN="${FLY_API_TOKEN:-}"
FLY_APP_NAME="${FLY_APP_NAME:-nexus}"
AGENT_TYPE="${AGENT_TYPE:-web_search}"
ITERATIONS=100
TARGET_P95_MS=50

# Test locations with expected regions
TEST_LOCATIONS=(
  "40.7128:-74.0060:ord:New York"
  "37.7749:-122.4194:sjc:San Francisco"
  "51.5074:-0.1278:lhr:London"
  "35.6762:139.6503:nrt:Tokyo"
)

echo -e "${GREEN}=== Phase 3 Latency Measurement Test ===${NC}"
echo ""

# Check prerequisites
if [ -z "$FLY_API_TOKEN" ]; then
  echo -e "${RED}Error: FLY_API_TOKEN environment variable not set${NC}"
  exit 1
fi

if ! command -v nexus-edge-orchestrator-cli &> /dev/null; then
  echo -e "${RED}Error: nexus-edge-orchestrator-cli not found in PATH${NC}"
  exit 1
fi

# Function to measure latency
measure_latency() {
  local lat=$1
  local lon=$2
  local region=$3
  local location_name=$4
  
  echo -e "${BLUE}Measuring latency for $location_name -> $region...${NC}"
  
  local latencies=()
  local success_count=0
  local fail_count=0
  
  for i in $(seq 1 $ITERATIONS); do
    start_time=$(date +%s%N)
    
    if result=$(nexus-edge-orchestrator-cli launch \
      --agent-type "$AGENT_TYPE" \
      --lat "$lat" \
      --lon "$lon" \
      2>/dev/null); then
      end_time=$(date +%s%N)
      latency_ms=$(( (end_time - start_time) / 1000000 ))
      latencies+=($latency_ms)
      ((success_count++))
      
      # Clean up: stop/delete the machine (would need machine ID from result)
      # For now, just measure launch latency
    else
      ((fail_count++))
    fi
    
    # Progress indicator
    if [ $((i % 10)) -eq 0 ]; then
      echo -n "."
    fi
  done
  
  echo ""
  
  if [ ${#latencies[@]} -eq 0 ]; then
    echo -e "  ${RED}✗ No successful measurements${NC}"
    return 1
  fi
  
  # Calculate statistics
  IFS=$'\n' sorted=($(sort -n <<<"${latencies[*]}"))
  unset IFS
  
  local count=${#sorted[@]}
  local p50_idx=$((count * 50 / 100))
  local p95_idx=$((count * 95 / 100))
  local p99_idx=$((count * 99 / 100))
  
  local p50=${sorted[$p50_idx]}
  local p95=${sorted[$p95_idx]}
  local p99=${sorted[$p99_idx]}
  
  # Calculate mean
  local sum=0
  for latency in "${latencies[@]}"; do
    sum=$((sum + latency))
  done
  local mean=$((sum / count))
  
  # Calculate min/max
  local min=${sorted[0]}
  local max=${sorted[$((count - 1))]}
  
  echo -e "  ${GREEN}Results for $location_name -> $region:${NC}"
  echo "    Success rate: $success_count/$ITERATIONS ($((success_count * 100 / ITERATIONS))%)"
  echo "    Mean latency: ${mean}ms"
  echo "    P50 latency:  ${p50}ms"
  echo "    P95 latency:  ${p95}ms"
  echo "    P99 latency:  ${p99}ms"
  echo "    Min latency:  ${min}ms"
  echo "    Max latency:  ${max}ms"
  
  # Check if P95 meets target
  if [ $p95 -le $TARGET_P95_MS ]; then
    echo -e "    ${GREEN}✓ P95 latency meets target (<${TARGET_P95_MS}ms)${NC}"
    return 0
  else
    echo -e "    ${YELLOW}⚠ P95 latency exceeds target (${p95}ms > ${TARGET_P95_MS}ms)${NC}"
    return 1
  fi
}

# Run latency tests for each location
echo -e "${YELLOW}Running latency tests ($ITERATIONS iterations per location)...${NC}"
echo ""

PASSED_TESTS=0
FAILED_TESTS=0

for test_location in "${TEST_LOCATIONS[@]}"; do
  IFS=':' read -r lat lon region location_name <<< "$test_location"
  
  if measure_latency "$lat" "$lon" "$region" "$location_name"; then
    ((PASSED_TESTS++))
  else
    ((FAILED_TESTS++))
  fi
  echo ""
done

# Summary
echo -e "${GREEN}=== Test Summary ===${NC}"
echo "Total locations tested: ${#TEST_LOCATIONS[@]}"
echo "Tests passed: $PASSED_TESTS"
echo "Tests failed: $FAILED_TESTS"
echo "Target P95 latency: ${TARGET_P95_MS}ms"
echo ""

if [ $FAILED_TESTS -eq 0 ]; then
  echo -e "${GREEN}✓ All latency tests passed!${NC}"
  exit 0
else
  echo -e "${YELLOW}⚠ Some latency tests failed${NC}"
  exit 1
fi
