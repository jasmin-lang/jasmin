#!/bin/bash
#
# Installation script for the Jasmin language on Ubuntu 24.04 (resolved dependency conflicts) and similar distributions.
#
# This script automates the setup process, addressing common dependency issues
# such as the removal of 'python3-distutils' in recent Ubuntu versions.
# It installs system dependencies, initializes OPAM with a specific OCaml version,
# installs provers and EasyCrypt, and finally compiles Jasmin from its
# source repository.
#

# Exit immediately if any command fails to ensure a safe and clean execution.
set -e

# --- Helper Functions for Colored Output ---
info() {
    # Blue color for informational messages
    echo -e "\033[1;34m[INFO]\033[0m $1"
}

success() {
    # Green color for success messages
    echo -e "\033[1;32m[SUCCESS]\033[0m $1"
}

warn() {
    # Yellow color for warnings
    echo -e "\033[1;33m[WARNING]\033[0m $1"
}

# --- 0. Clean Up (Optional) ---
if [ -d "$HOME/.opam" ]; then
    warn "An existing OPAM setup was found."
    read -p "Do you want to remove it to start fresh (recommended)? (y/N) " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        info "Removing ~/.opam..."
        rm -rf "$HOME/.opam"
        success "Cleaned up old OPAM root."
    fi
fi

# --- 1. Install System Dependencies ---
info "Updating package list and installing system dependencies..."
sudo apt-get update
sudo apt-get install -y \
    build-essential \
    opam \
    cvc4 \
    pkg-config \
    libgmp-dev \
    libpcre3-dev \
    zlib1g-dev \
    libmpfr-dev \
    libppl-dev \
    autoconf \
    python3-setuptools \
    git \
    m4

# --- 2. Initialize OPAM (OCaml Package Manager) ---
info "Initializing OPAM with OCaml 4.14.2..."
# Check if OPAM is already initialized to avoid re-initializing.
if [ -d "$HOME/.opam" ]; then
    warn "Existing OPAM root found at ~/.opam. The script will use it."
else
    # Initialize OPAM non-interactively with OCaml 4.14.2 to satisfy dependencies.
    opam init -a --disable-sandboxing -c ocaml-base-compiler.4.14.2
fi

# Set up the necessary environment variables for the current shell session.
eval $(opam env)

info "Current OCaml version: $(ocaml -version)"
info "OPAM environment is configured for this session."

# --- 3. Install Provers and EasyCrypt ---
info "Adding the Coq OPAM repository..."
opam repo add coq-released https://coq.inria.fr/opam/released

info "Pinning EasyCrypt and coq-mathcomp-word to specific repository versions..."
# Pinning ensures we get specific, compatible versions directly from their git repos.
opam pin -yn add easycrypt https://github.com/EasyCrypt/easycrypt.git
opam pin -yn add coq-mathcomp-word https://github.com/jasmin-lang/coqword.git

info "Installing specific versions of the Alt-Ergo and Z3 provers..."
# Alt-Ergo installs normally.
opam install -y alt-ergo.2.4.1
# The z3.4.11.0 opam package has an outdated system dependency check for 'python3-distutils'.
# Since we installed 'python3-setuptools', the required functionality is present.
# The '--no-depexts' flag tells opam to skip the faulty check and proceed.
opam install -y z3.4.11.0 --no-depexts


info "Installing EasyCrypt. This may take a significant amount of time..."
# This command pulls in Coq and many other large dependencies.
opam install -y easycrypt

info "Configuring Why3 prover platform for EasyCrypt..."
easycrypt why3config

# --- 4. Clone and Build Jasmin ---
JASMIN_DIR="$HOME/jasmin"
info "Cloning Jasmin repository into $JASMIN_DIR..."

# Check if the directory already exists to prevent errors.
if [ -d "$JASMIN_DIR" ]; then
    warn "Jasmin directory already exists. Pulling the latest changes."
    cd "$JASMIN_DIR"
    git pull
else
    git clone https://github.com/jasmin-lang/jasmin.git "$JASMIN_DIR"
    cd "$JASMIN_DIR"
fi

info "Installing Jasmin's dependencies via OPAM..."
# Install dependencies using the 'opam' file in the cloned repository.
opam install . --deps-only -y

info "Building the Jasmin compiler..."
# The build process requires specific make targets.
cd compiler
make CIL
make

# --- 5. Final Configuration ---
info "Configuring EasyCrypt to locate the Jasmin library..."
EASYCRYPT_CONF_DIR="$HOME/.config/easycrypt"
mkdir -p "$EASYCRYPT_CONF_DIR"
# Create the configuration file with the correct path to Jasmin's 'eclib'.
echo -e "[general]\nidirs=Jasmin:$JASMIN_DIR/eclib" > "$EASYCRYPT_CONF_DIR/easycrypt.conf"

# --- Completion ---
success "Jasmin installation and configuration complete!"
info "The Jasmin compiler executable is located at: $JASMIN_DIR/compiler/jasmin"
info "To use the 'opam' environment in new terminal sessions, you must run: eval \$(opam env)"
info "For convenience, you can add this command to your shell startup file (e.g., ~/.bashrc)."
read -p "Add 'eval \$(opam env)' to ~/.bashrc? (y/N) " -n 1 -r
echo
if [[ $REPLY =~ ^[Yy]$ ]]; then
    echo -e '\n# Set up OPAM environment\neval $(opam env)' >> "$HOME/.bashrc"
    success "Added 'eval \$(opam env)' to ~/.bashrc. Please run 'source ~/.bashrc' or open a new terminal."
fi
