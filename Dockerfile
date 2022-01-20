ARG MATLAB_VERSION=r2021b

FROM mathworks/matlab-deps:${MATLAB_VERSION}

ARG SCALA_VERSION=2.12.8
ARG SBT_VERSION=1.3.7
ARG WOLFRAM_ENGINE_PATH=/usr/local/Wolfram/WolframEngine
ARG DEBIAN_FRONTEND=noninteractive
ARG USER_NAME
ENV TZ=America/New_York

# Add user and grant sudo permission.
RUN adduser --shell /bin/bash --disabled-password --gecos "" ${USER_NAME} && \
    echo "${USER_NAME} ALL=(ALL) NOPASSWD: ALL" > /etc/sudoers.d/${USER_NAME} && \
    chmod 0440 /etc/sudoers.d/${USER_NAME}

# repeat MATLAB_VERSION, otherwise it's not available in Matlab install below
ARG MATLAB_VERSION

# Install requirements
RUN apt-get --yes update && \
  apt-get --yes upgrade && \
  apt-get --no-install-recommends --yes install \
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
    ca-certificates && \
  apt-get clean && \
  apt-get autoremove && \
  rm -rf /var/lib/apt/lists/*

USER ${USER_NAME}
WORKDIR /home/${USER_NAME}

# Install MATLAB
RUN wget https://www.mathworks.com/mpm/glnxa64/mpm && \
    chmod +x mpm && \
    sudo ./mpm install \
        --release=${MATLAB_VERSION} \
        --destination=/opt/matlab \
        --products=MATLAB && \
    sudo rm -f mpm /tmp/mathworks_root.log && \
    sudo ln -s /opt/matlab/bin/matlab /usr/local/bin/matlab

# Activate MATLAB
ARG LICENSE_FILE
COPY ${LICENSE_FILE} /opt/matlab/licenses/

# Install MATLAB package manager
RUN wget https://github.com/mobeets/mpm/archive/refs/tags/v3.1.0.zip && \
  unzip v3.1.0.zip

# Download sostools
RUN wget https://github.com/oxfordcontrol/SOSTOOLS/archive/refs/tags/v4.01.zip && \
  unzip v4.01.zip

RUN sudo systemctl enable avahi-daemon

# Install Scala
WORKDIR /tmp/
RUN wget -P /tmp https://www.scala-lang.org/files/archive/scala-${SCALA_VERSION}.deb && \
  sudo dpkg -i scala-${SCALA_VERSION}.deb && \
  sudo apt-get --yes update && \
  sudo apt-get --yes upgrade && \
  sudo apt-get --yes install scala && \
  sudo apt-get clean && \
  sudo apt-get autoremove && \
  rm scala-${SCALA_VERSION}.deb

# Install SBT
RUN wget https://scala.jfrog.io/artifactory/debian/sbt-${SBT_VERSION}.deb && \
  sudo dpkg -i sbt-${SBT_VERSION}.deb && \
  sudo apt-get --yes update && \
  sudo apt-get --yes upgrade && \
  sudo apt-get --yes install sbt && \
  rm sbt-${SBT_VERSION}.deb

# Install Wolfram Engine
RUN sudo bash -c 'echo "en_US.UTF-8 UTF-8" > /etc/locale.gen' && \
  sudo locale-gen
RUN wget https://account.wolfram.com/download/public/wolfram-engine/desktop/LINUX && \
  sudo bash LINUX -- -auto -verbose && \
  rm LINUX

# Pull KeYmaera X
WORKDIR /home/${USER_NAME}/
# avoid caching git clone by adding the latest commit SHA to the container
ADD https://api.github.com/repos/LS-Lab/KeYmaeraX-release/git/refs/heads/master kyx-version.json
RUN git clone --depth 1 https://github.com/LS-Lab/KeYmaeraX-release.git
ADD https://api.github.com/repos/LS-Lab/KeYmaeraX-projects/git/refs/heads/master projects-version.json
WORKDIR /home/${USER_NAME}/KeYmaeraX-release/keymaerax-webui/src/main/resources/
RUN git clone --depth 1 https://github.com/LS-Lab/KeYmaeraX-projects.git

# Build KeYmaera X
WORKDIR /home/${USER_NAME}/KeYmaeraX-release/
RUN ls ${WOLFRAM_ENGINE_PATH} > weversion.txt
RUN bash -l -c "echo \"mathematica.jlink.path=${WOLFRAM_ENGINE_PATH}/"'$(<weversion.txt)/SystemFiles/Links/JLink/JLink.jar" > local.properties'
RUN sbt clean assembly
RUN cp keymaerax-webui/target/scala-2.12/KeYmaeraX*.jar /home/${USER_NAME}/keymaerax.jar

# Download and install MATLink
WORKDIR /home/${USER_NAME}/
RUN wget http://download.matlink.org/MATLink.zip && \
  mkdir -p .WolframEngine/Applications/ && \
  unzip MATLink.zip -d .WolframEngine/Applications/

# Add Wolfram Engine to the path
#ENV PATH="${WOLFRAM_ENGINE_PATH}/"'$(<weversion.txt)/Executables/:'"$PATH"
ENV PATH="${WOLFRAM_ENGINE_PATH}/13.0/Executables:$PATH"

# Install MATLink dependencies
RUN sudo apt-get --yes update && \
  sudo apt-get --yes upgrade && \
  sudo apt-get --no-install-recommends --yes install \
    g++ \
    uuid-dev \
    csh && \
  sudo apt-get clean && \
  sudo apt-get autoremove && \
  sudo rm -rf /var/lib/apt/lists/*

# Set final working directory
WORKDIR /home/${USER_NAME}/
