FROM ubuntu:24.04

# This Dockerfile does not add a user. It has to be defined in the run command -- see below and in the docker-run.sh script

#docker run --rm -it \
#  -e DISPLAY=$DISPLAY_ENV \
#  -v /tmp/.X11-unix:/tmp/.X11-unix \
#  -v "$LOCAL_ONTOLOGY_REPOSITORY:$DOKER_ONTOLOGY_REPOSITORY" \
#  -u 1000:1000 \
#  --network="host" \
#  "$IMAGE_NAME" "${CMD[@]}"

# to get root access:
# docker run -u 0 -it periconto bash




# Install Python dependencies using apt for better compatibility with system packages
RUN apt-get update && apt-get install -y --no-install-recommends \
    python3 \
    python3-pip \
    python3-pyqt6 \
    python3-pyqt6.qtsvg \
    python3-graphviz \
    python3-rdflib \
    graphviz \
    evince \
    qpdfview \
    libcanberra-gtk-module \
    libcanberra-gtk3-module \
    sudo \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*


ENV DEBIAN_FRONTEND=noninteractive \
    PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    XDG_RUNTIME_DIR=/tmp/runtime-appuser \
    QT_LOGGING_RULES="*.debug=false;qt.qpa.*=false"

# Create runtime directory with correct permissions
RUN mkdir -p /tmp/runtime-appuser && \
    chmod 700 /tmp/runtime-appuser

# Install dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    libgl1 \
    libegl1 \
    libxkbcommon-x11-0 \
    libxcb-icccm4 \
    libxcb-image0 \
    libxcb-keysyms1 \
    libxcb-randr0 \
    libxcb-render-util0 \
    libxcb-xinerama0 \
    libxcb-xkb1 \
    libxcb-shape0 \
    libxcb-shm0 \
    libxcb-sync1 \
    libxcb-xfixes0 \
    libsm6 \
    libice6 \
    x11-utils \
    dbus \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*


# Create app directory structure
RUN mkdir -p /app/src
WORKDIR /app

# Copy the application
COPY --chown=appuser:appuser src/ /app/src/
RUN chmod +x /app/src/BricksSchemata.py /app/src/TreeSchemata.py

# allow evince to generate directory /tmp/runtime-appuser/dconf
RUN chmod -R 777 /tmp/runtime-appuser

#RUN mkdir -r /run/user/1000/at-spi/bus_0 # did not work -- remains an error message

# Set environment variables for X11 forwarding
ENV DISPLAY=:0
ENV QT_X11_NO_MITSHM=1
ENV QT_QPA_PLATFORM=xcb

ENV NO_AT_BRIDGE=1

# what is run is defined in the docker-run.sh script
WORKDIR /app/src
