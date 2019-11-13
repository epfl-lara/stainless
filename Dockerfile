FROM openjdk:8u222-jre-slim-buster

WORKDIR /app

RUN apt-get update && apt-get install -y wget unzip libgomp1

ARG STAINLESS_VERSION

RUN echo "Fetching https://github.com/epfl-lara/stainless/releases/download/v$STAINLESS_VERSION/stainless-scalac-standalone-$STAINLESS_VERSION-linux.zip"
RUN wget --quiet https://github.com/epfl-lara/stainless/releases/download/v$STAINLESS_VERSION/stainless-scalac-standalone-$STAINLESS_VERSION-linux.zip
RUN echo "Unzipping stainless-scalac-standalone-$STAINLESS_VERSION-linux.zip"
RUN unzip stainless-scalac-standalone-$STAINLESS_VERSION-linux.zip && rm -f stainless-scalac-standalone-$STAINLESS_VERSION-linux.zip

ENTRYPOINT ["/app/stainless"]

