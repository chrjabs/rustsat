#!/usr/bin/env bash

ORGANIZATION="$ORGANIZATION"
REPOSITORY="$REPOSITORY"
ACCESS_TOKEN="$ACCESS_TOKEN"

if [ -n "$REPOSITORY" ]; then
  REG_TOKEN=$(curl -sSL \
    -X POST \
    -H "Accept: application/vnd.github+json" \
    -H "Authorization: Bearer ${ACCESS_TOKEN}" \
    -H "X-GitHub-Api-Version: 2022-11-28" \
    "https://api.github.com/repos/${ORGANIZATION}/${REPOSITORY}/actions/runners/registration-token" | \
    jq .token --raw-output)
  URL="https://github.com/${ORGANIZATION}/${REPOSITORY}"
else
  REG_TOKEN=$(curl -sSL \
    -X POST \
    -H "Accept: application/vnd.github+json" \
    -H "Authorization: Bearer ${ACCESS_TOKEN}" \
    -H "X-GitHub-Api-Version: 2022-11-28" \
    "https://api.github.com/orgs/${ORGANIZATION}/actions/runners/registration-token" | \
    jq .token --raw-output)
  URL="https://github.com/${ORGANIZATION}"
fi

./config.sh --unattended --url "${URL}" --token "${REG_TOKEN}"

cleanup() {
  echo "Removing runner..."
  ./config.sh remove --token "${REG_TOKEN}"
}

trap 'cleanup; exit 130' INT
trap 'cleanup; exit 143' TERM

./run.sh & wait $!
