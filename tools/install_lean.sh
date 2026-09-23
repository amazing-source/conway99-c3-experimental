#!/usr/bin/env bash
# Installs elan (Lean toolchain manager) and a Mathlib-based Lake project inside the lab.
set -u
LAB=/c/home/researcher/Desktop/c3_experimental
cd "$LAB/tools" || exit 1
echo "[$(date -Is)] download elan"
curl -sSL -o elan.zip https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-pc-windows-msvc.zip || exit 2
python -c "import zipfile; zipfile.ZipFile('elan.zip').extractall('elan_pkg')" || exit 3
ls -la elan_pkg
echo "[$(date -Is)] run elan-init"
./elan_pkg/elan-init.exe -y --default-toolchain none || exit 4
export PATH="$HOME/.elan/bin:$PATH"
elan --version
cd "$LAB" || exit 1
if [ ! -d c3formal ]; then
  echo "[$(date -Is)] lake new c3formal math (mathlib toolchain)"
  lake +leanprover-community/mathlib4:lean-toolchain new c3formal math || exit 5
fi
cd c3formal || exit 1
cat lean-toolchain
echo "[$(date -Is)] lake exe cache get"
lake exe cache get || exit 6
echo "[$(date -Is)] lake build"
lake build || exit 7
echo "[$(date -Is)] DONE"
