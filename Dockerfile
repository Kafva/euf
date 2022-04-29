FROM euf-base
# EUF needs to be able to build the dependency that it analyzes
# and additional dependencies may need to be installed as a conseqeunce
USER root
RUN apt-get update && apt-get upgrade -y && apt-get install -y \
  libidn11-dev libudns-dev libgsasl7-dev

USER euf
WORKDIR /home/euf/euf

# 'RUN true' is used to avoid build failures when
# the files to copy have not changed (and therefore
# do not create a new layer)
COPY --chown=euf:root scripts/*.sh ./scripts/
RUN true
COPY --chown=euf:root euf.py ./
RUN true
COPY --chown=euf:root src/*.py ./src/

USER euf
ENTRYPOINT ["./euf.py"]
