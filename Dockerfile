# $ docker build -t asplos-rsbsecure:latest -f Dockerfile .

FROM debian:stable-slim

ARG USERNAME=asplos
SHELL ["/bin/bash", "-c"]
ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get --quiet --assume-yes update && \
    apt-get --quiet --assume-yes upgrade && \
    apt-get --quiet --assume-yes install apt-utils && \
    apt-get --quiet --assume-yes install sudo wget curl git time xz-utils libicu-dev

RUN apt-get --quiet --assume-yes install ocaml ocaml-native-compilers camlp4-extra opam && \
    apt-get --quiet --assume-yes install autoconf debianutils libgmp-dev pkg-config zlib1g-dev

RUN apt-get --quiet --assume-yes install vim build-essential python3 python3-pip m4 libgsl-dev libpcre3-dev jq parallel valgrind

RUN apt-get --quiet --assume-yes clean

RUN echo "%sudo  ALL=(ALL) NOPASSWD: ALL" > /etc/sudoers.d/sudoers && \
    chown root:root /etc/sudoers.d/sudoers && \
    chmod 0400 /etc/sudoers.d/sudoers && \
    useradd --create-home --shell /bin/bash --home-dir /home/$USERNAME --gid root --groups sudo --uid 1001 $USERNAME


USER $USERNAME
WORKDIR /home/$USERNAME
COPY . /home/$USERNAME/

RUN curl -L https://nixos.org/nix/install > nix-install && \
    sh nix-install && rm nix-install && \
    USER=asplos source $HOME/.nix-profile/etc/profile.d/nix.sh && \
    nix-channel --update && \
    (cd jasmin/ && nix-shell --command "(cd compiler && make -j$(nproc) CIL && make)") && \
    sudo install -D jasmin/compiler/jasminc /usr/local/bin/
