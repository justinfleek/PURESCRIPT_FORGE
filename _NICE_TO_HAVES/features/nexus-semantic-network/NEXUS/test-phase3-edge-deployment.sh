#!/bin/bash
# | Phase 3 Edge Deployment Test Script
# | Tests agent deployment to multiple Fly.io regions

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Configuration
FLY_API_TOKEN="${FLY_API_TOKEN:-}"
FLY_APP_NAME="${FLY_APP_NAME:-nexus}"
AGENT_TYPE="${AGENT_TYPE:-web_search}"
REGIONS=("ord" "sjc" "lhr" "nrt")

# Test locations (latitude, longitude, expected region)
# New York -> ORD (Chicago)
TEST_LOCATIONS=(
  "40.7128:-74.0060:ord"
  # San Francisco -> SJC (San Jose)
  "37.7749:-122.4194:sjc"
  # London -> LHR (London)
  "51.5074:-0.1278:lhr"
  # Tokyo -> NRT (Tokyo)
  "35.6762:139.6503:nrt"
)

echo -e "${GREEN}=== Phase 3 Edge Deployment Test ===${NC}"
echo ""

# Check prerequisites
if [ -z "$FLY_API_TOKEN" ]; then
  echo -e "${RED}Error: FLY_API_TOKEN environment variable not set${NC}"
  exit 1
fi

if ! command -v nexus-edge-orchestrator-cli &> /dev/null; then
  echo -e "${RED}Error: nexus-edge-orchestrator-cli not found in PATH${NC}"
  echo "Please build the Haskell edge orchestrator first:"
  echo "  cd NEXUS/agent-orchestrator-edge-hs"
  echo "  cabal build"
  exit 1
fi

# Test 1: List available regions
echo -e "${YELLOW}[Test 1] Listing available regions...${NC}"
if nexus-edge-orchestrator-cli list-regions > /tmp/regions.json 2>&1; then
  echo -e "${GREEN}✓ Regions listed successfully${NC}"
  cat /tmp/regions.json | jq '.' || cat /tmp/regions.json
else
  echo -e "${RED}✗ Failed to list regions${NC}"
  exit 1
fi
echo ""

# Test 2: Deploy agents to each region explicitly
echo -e "${YELLOW}[Test 2] Deploying agents to each region...${NC}"
MACHINE_IDS=()

for region in "${REGIONS[@]}"; do
  echo -e "  Deploying to region: ${region}"
  
  # Launch agent in specific region
  if result=$(nexus-edge-orchestrator-cli launch \
    --agent-type "$AGENT_TYPE" \
    --region "$region" \
    2>&1); then
    machine_id=$(echo "$result" | jq -r '.machineId // .agentId // empty' 2>/dev/null || echo "")
    if [ -n "$machine_id" ]; then
      MACHINE_IDS+=("$machine_id")
      echo -e "    ${GREEN}✓ Agent deployed: $machine_id${NC}"
    else
      echo -e "    ${YELLOW}⚠ Response received but machine ID not found${NC}"
      echo "    Response: $result"
    fi
  else
    echo -e "    ${RED}✗ Failed to deploy to $region${NC}"
    echo "    Error: $result"
  fi
  echo ""
done

# Test 3: Test location-based region selection
echo -e "${YELLOW}[Test 3] Testing location-based region selection...${NC}"
for test_location in "${TEST_LOCATIONS[@]}"; do
  IFS=':' read -r lat lon expected_region <<< "$test_location"
  echo -e "  Testing location: ($lat, $lon) -> Expected: $expected_region"
  
  if result=$(nexus-edge-orchestrator-cli launch \
    --agent-type "$AGENT_TYPE" \
    --lat "$lat" \
    --lon "$lon" \
    2>&1); then
    selected_region=$(echo "$result" | jq -r '.region // empty' 2>/dev/null || echo "")
    if [ "$selected_region" = "$expected_region" ]; then
      echo -e "    ${GREEN}✓ Correct region selected: $selected_region${NC}"
    else
      echo -e "    ${YELLOW}⚠ Region mismatch: expected $expected_region, got $selected_region${NC}"
    fi
  else
    echo -e "    ${RED}✗ Failed to launch agent${NC}"
    echo "    Error: $result"
  fi
  echo ""
done

# Test 4: Check agent status
echo -e "${YELLOW}[Test 4] Checking agent status...${NC}"
for machine_id in "${MACHINE_IDS[@]}"; do
  if [ -n "$machine_id" ]; then
    echo -e "  Checking machine: $machine_id"
    if status=$(nexus-edge-orchestrator-cli status "$machine_id" 2>&1); then
      echo -e "    ${GREEN}✓ Status retrieved${NC}"
      echo "$status" | jq '.' 2>/dev/null || echo "$status"
    else
      echo -e "    ${RED}✗ Failed to get status${NC}"
      echo "    Error: $status"
    fi
    echo ""
  fi
done

echo -e "${GREEN}=== Test Summary ===${NC}"
echo "Regions tested: ${#REGIONS[@]}"
echo "Machines deployed: ${#MACHINE_IDS[@]}"
echo "Location tests: ${#TEST_LOCATIONS[@]}"
echo ""
echo -e "${GREEN}Phase 3 deployment test completed!${NC}"
