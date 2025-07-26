#!/bin/bash
DOCKER_USERNAME="hapdocker"

echo "$DOCKER_ACCESS_TOKEN" | docker login -u $DOCKER_USERNAME --password-stdin
# docker login --username hapdocker
docker push hapdocker/periconto:latest

mail -s "pushed PeriConto" "heinz.preisig@chemeng.ntnu.no"
