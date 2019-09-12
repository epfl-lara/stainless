FROM openjdk:8-jdk

WORKDIR /app

RUN apt-get update && apt-get install -y apt-utils libgomp1

RUN wget https://github.com/epfl-lara/stainless/releases/download/v0.5.1/stainless-scalac-standalone-0.5.1-linux.zip
RUN unzip stainless-scalac-standalone-0.5.1-linux.zip

ENTRYPOINT ["/app/stainless"]

