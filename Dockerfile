FROM eclipse-temurin:17-jre-noble

WORKDIR /app

RUN apt-get update && apt-get install -y wget unzip libgomp1

ARG STAINLESS_VERSION

RUN echo "Fetching https://github.com/epfl-lara/stainless/releases/download/v$STAINLESS_VERSION/stainless-dotty-standalone-$STAINLESS_VERSION-linux.zip"
RUN wget --quiet https://github.com/epfl-lara/stainless/releases/download/v$STAINLESS_VERSION/stainless-dotty-standalone-$STAINLESS_VERSION-linux.zip
RUN echo "Unzipping stainless-dotty-standalone-$STAINLESS_VERSION-linux.zip"
RUN unzip stainless-dotty-standalone-$STAINLESS_VERSION-linux.zip && rm -f stainless-dotty-standalone-$STAINLESS_VERSION-linux.zip

ENTRYPOINT ["/app/stainless"]

