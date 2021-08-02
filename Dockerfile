FROM ubuntu:18.04

ARG SCALA_VERSION=2.12.8
ARG SBT_VERSION=1.3.7
ARG WOLFRAM_ENGINE_PATH=/usr/local/Wolfram/WolframEngine
ARG DEBIAN_FRONTEND="noninteractive"
ENV TZ=America/New_York

# Install requirements
RUN apt-get -y update && apt-get -y upgrade && apt-get -y install \
    apt-utils \
    software-properties-common \
    curl \
    avahi-daemon \
    wget \
    unzip \
    zip \
    build-essential \
    openjdk-8-jre-headless \
    openjdk-8-jdk \
    git \
    sshpass \
    sudo \
    locales \
    locales-all \
    ssh \
    vim \
    expect \
    libfontconfig1 \
    libgl1-mesa-glx \
    libasound2 \
    util-linux \
    && rm -rf /var/lib/apt/lists/*

RUN systemctl enable avahi-daemon

# Install Scala
WORKDIR /tmp/
RUN wget -P /tmp https://www.scala-lang.org/files/archive/scala-${SCALA_VERSION}.deb && \
  dpkg -i scala-${SCALA_VERSION}.deb && \
  apt-get -y update && apt-get -y upgrade && apt-get -y install scala && \
  rm scala-${SCALA_VERSION}.deb

# Install SBT
RUN wget https://scala.jfrog.io/artifactory/debian/sbt-${SBT_VERSION}.deb && \
  dpkg -i sbt-${SBT_VERSION}.deb && \
  apt-get -y update && apt-get -y upgrade && apt-get -y install sbt && \
  rm sbt-${SBT_VERSION}.deb

# Install Wolfram Engine
RUN echo "en_US.UTF-8 UTF-8" > /etc/locale.gen && locale-gen
RUN wget https://account.wolfram.com/download/public/wolfram-engine/desktop/LINUX && \
  sudo bash LINUX -- -auto -verbose && \
  rm LINUX

# Pull KeYmaera X
WORKDIR /root/
# avoid caching git clone by adding the latest commit SHA to the container
ADD https://api.github.com/repos/LS-Lab/KeYmaeraX-release/git/refs/heads/master kyx-version.json
RUN git clone --depth 1 https://github.com/LS-Lab/KeYmaeraX-release.git
ADD https://api.github.com/repos/LS-Lab/KeYmaeraX-projects/git/refs/heads/master projects-version.json
WORKDIR /root/KeYmaeraX-release/keymaerax-webui/src/main/resources/
RUN git clone --depth 1 https://github.com/LS-Lab/KeYmaeraX-projects.git

# Build KeYmaera X
WORKDIR /root/KeYmaeraX-release/
RUN ls ${WOLFRAM_ENGINE_PATH} > weversion.txt
RUN bash -l -c "echo \"mathematica.jlink.path=${WOLFRAM_ENGINE_PATH}/"'$(<weversion.txt)/SystemFiles/Links/JLink/JLink.jar" > local.properties'
RUN sbt clean assembly
RUN cp keymaerax-webui/target/scala-2.12/KeYmaeraX*.jar /root/keymaerax.jar

# Set final working directory
WORKDIR /root/
