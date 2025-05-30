FROM rust:1.86-bookworm

ENV CI=true

# Install Rust components and toolchains
RUN rustup install nightly-2025-05-02 --component clippy,rustfmt,llvm-tools-preview,miri && \
    # MSRVs
    rustup install --profile minimal 1.75 && rustup install --profile minimal 1.76 && rustup install --profile minimal 1.77

# Install CI dependencies
RUN apt-get update && apt-get install -y \
    # Script dependencies
    curl git jq rsync \
    # Rust build dependencies
    libssl-dev pkg-config valgrind \
    # VeriPB dependencies
    libgmp-dev \
    # C(++) build dependencies
    make cmake llvm libclang-dev clang clang-format \
    # Python dependencies
    python3 python3-pip pipx python3-dev && \
    # Install cargo-binstall using curl
    curl -L --proto '=https' --tlsv1.2 -sSf https://raw.githubusercontent.com/cargo-bins/cargo-binstall/main/install-from-binstall-release.sh | bash && \
    # Clean up - remove apt cache
    apt-get autoremove -y && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

# Clang as default
ENV CC=clang
ENV CXX=clang++

ARG GH_VERSION="2.70.0"

# Install CI tools using cargo-binstall
RUN cargo binstall -y cargo-nextest cargo-hack cargo-rdme cargo-spellcheck cargo-semver-checks cargo-llvm-cov cargo-valgrind just release-plz typos-cli && \
    # Install Python tools with pipx
    mkdir /opt/pipx && export PIPX_HOME=/opt/pipx && export PIPX_BIN_DIR=/usr/local/bin && \
    pipx install maturin && \
    # Install VeriPB
    pipx install https://gitlab.com/MIAOresearch/software/VeriPB/-/archive/version2/VeriPB-version2.zip && \
    # Install GH
    mkdir /tmp/gh && curl -sSL -o /tmp/gh/gh.tar.gz https://github.com/cli/cli/releases/download/v${GH_VERSION}/gh_${GH_VERSION}_linux_amd64.tar.gz && \
    cd /tmp/gh && tar xvf gh.tar.gz && cp gh_${GH_VERSION}_linux_amd64/bin/gh /usr/local/bin/gh && \
    rm -rf /tmp/gh

ENV VERIPB_CHECKER=/usr/local/bin/veripb

ARG KISSAT_VERSION="4.0.2"
ARG CADICAL_VERSION="2.1.3"

# Install some SAT solver binaries
RUN mkdir /tmp/gimsatul && curl -o /tmp/gimsatul/src.zip -L https://github.com/arminbiere/gimsatul/archive/refs/heads/master.zip && \
    cd /tmp/gimsatul && unzip src.zip && cd gimsatul-master && ./configure && make && \
    mv /tmp/gimsatul/gimsatul-master/gimsatul /usr/local/bin/gimsatul && rm -rf /tmp/gimsatul && \
    mkdir /tmp/kissat && curl -o /tmp/kissat/src.zip -L https://github.com/arminbiere/kissat/archive/refs/tags/rel-${KISSAT_VERSION}.zip && \
    cd /tmp/kissat && unzip src.zip && cd kissat-rel-${KISSAT_VERSION} && ./configure && make && \
    mv /tmp/kissat/kissat-rel-${KISSAT_VERSION}/build/kissat /usr/local/bin/kissat && rm -rf /tmp/kissat && \
    mkdir /tmp/cadical && curl -o /tmp/cadical/src.zip -L https://github.com/arminbiere/cadical/archive/refs/tags/rel-${CADICAL_VERSION}.zip && \
    cd /tmp/cadical && unzip src.zip && cd cadical-rel-${CADICAL_VERSION} && ./configure && make && \
    mv /tmp/cadical/cadical-rel-${CADICAL_VERSION}/build/cadical /usr/local/bin/cadical && rm -rf /tmp/cadical

# Set environment variables
ENV CARGO_HOME=/runner/.cargo
ENV CARGO_INCREMENTAL=0
ENV CLICOLOR=1
ENV ORGANIZATION=chrjabs
ENV REPOSITORY=rustsat

ARG RUNNER_VERSION="2.323.0"
ENV RUNNER_VERSION=${RUNNER_VERSION}

# Create a work directory
WORKDIR /runner

# Setup user for github runner
RUN useradd -m runner && mkdir actions-runner && cd actions-runner && \
    # Install github runner
    curl -O -L https://github.com/actions/runner/releases/download/v${RUNNER_VERSION}/actions-runner-linux-x64-${RUNNER_VERSION}.tar.gz && \
    tar xzf ./actions-runner-linux-x64-${RUNNER_VERSION}.tar.gz && rm ./actions-runner-linux-x64-${RUNNER_VERSION}.tar.gz && \
    cp -a /runner/actions-runner/. /runner && rm -rf /runner/actions-runner/ && \
    # Install dependencies
    mkdir /runner/cache && chown -R runner /runner && /runner/bin/installdependencies.sh && \
    # Clean up
    apt-get autoremove -y && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

VOLUME /runner/cache
ENV CACHE=/runner/cache

USER runner

# Setup Python-API job venv
RUN python3 -m venv /runner/python-api-venv && /runner/python-api-venv/bin/python -m pip install mypy && \
    # Setup pages job venv
    python3 -m venv /runner/pages-venv && /runner/pages-venv/bin/python -m pip install pdoc

ENV PYTHON_API_VENV=/runner/python-api-venv
ENV PAGES_VENV=/runner/pages-venv

COPY --chmod=0755 start.sh start.sh
COPY --chmod=0755 cache.sh cache.sh

CMD ["/runner/start.sh"]

LABEL org.opencontainers.image.source="https://github.com/chrjabs/rustsat"
