#!/usr/bin/env python3
"""
Railway Auto-Deploy and Automated Domain Generator
--------------------------------------------------
This script automates deploying the Shopify Checker to Railway and
automatically generating a public domain (*.up.railway.app).
"""

import os
import shutil
import subprocess
import sys

def run_cmd(cmd, check=True):
    print(f"\n[EXEC] {' '.join(cmd) if isinstance(cmd, list) else cmd}")
    res = subprocess.run(cmd, shell=isinstance(cmd, str), capture_output=True, text=True)
    if res.stdout:
        print(res.stdout.strip())
    if res.stderr and res.returncode != 0:
        print(f"[ERR] {res.stderr.strip()}", file=sys.stderr)
    if check and res.returncode != 0:
        raise RuntimeError(f"Command failed with code {res.returncode}")
    return res

def main():
    print("=" * 60)
    print(" 🚀 Railway Automated Deploy & Domain Generator")
    print("=" * 60)

    # 1. Check if Railway CLI is installed
    railway_bin = shutil.which("railway")
    if not railway_bin:
        print("\n[!] Railway CLI is not found in PATH.")
        print("    Install it easily with one of the following commands:")
        print("      • npm i -g @railway/cli")
        print("      • or brew install railway (macOS)")
        print("      • or iwr https://railway.com/install.ps1 -useb | iex (Windows PowerShell)\n")
        print("    After installing, run: railway login")
        print("    Then re-run this script to automatically deploy and generate your domain!")
        sys.exit(1)

    print(f"✓ Found Railway CLI at: {railway_bin}")

    # 2. Check Railway authentication
    whoami = run_cmd(["railway", "whoami"], check=False)
    if whoami.returncode != 0:
        print("\n[!] You are not logged in to Railway. Running 'railway login'...")
        run_cmd(["railway", "login"])

    # 3. Initialize or link project
    status = run_cmd(["railway", "status"], check=False)
    if status.returncode != 0 or "No project" in status.stdout:
        print("\n[+] Initializing new Railway project...")
        run_cmd(["railway", "init"])

    # 4. Deploy service
    print("\n[+] Deploying code to Railway...")
    run_cmd(["railway", "up", "--detach"])

    # 5. Automatically generate public domain
    print("\n[+] Automatically generating public Railway domain...")
    domain_res = run_cmd(["railway", "domain"], check=False)
    if domain_res.returncode == 0:
        print("\n" + "=" * 60)
        print(" 🎉 SUCCESS! Your application is live with an automatic domain:")
        print(f"    {domain_res.stdout.strip()}")
        print("=" * 60)
    else:
        print("\n[!] Note: If domain generation failed, verify service status in Railway dashboard:")
        print("    Railway Dashboard -> Settings -> Networking -> Click 'Generate Domain'")

if __name__ == "__main__":
    main()
