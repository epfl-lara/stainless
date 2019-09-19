FROM openjdk:8u222-jre-slim-buster

WORKDIR /app

RUN apt-get update && apt-get install -y wget unzip libgomp1

RUN wget --quiet https://github.com/epfl-lara/stainless/releases/download/v0.5.1/stainless-scalac-standalone-0.5.1-linux.zip
RUN unzip stainless-scalac-standalone-0.5.1-linux.zip && rm -f stainless-scalac-standalone-0.5.1-linux.zip

ENTRYPOINT ["/app/stainless"]

