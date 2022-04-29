FROM euf-base
# EUF needs to be able to build the dependency that it analyzes
# and additional dependencies may need to be installed as a conseqeunce
USER root
RUN apt-get update && apt-get upgrade -y && apt-get install -y \
  libidn11-dev libudns-dev libgsasl7-dev

# Update source files
USER euf
COPY . .

ENTRYPOINT ["./euf.py"]
