# To compile llvm2smt we need a ocaml version before or equal to 4.05 (cgum uses the `num` package which is now deprecated)
# Setup of llvm2smt (on FreeBSD):	
FROM ocaml/opam:alpine-3.15-ocaml-4.05-flambda

RUN sudo apk update
RUN git clone https://github.com/SRI-CSL/llvm2smt.git

ENV PATH=${PATH}:/home/opam/.opam/4.05/bin/

RUN make -C llvm2smt/src
RUN sudo bash -c 'mv /home/opam/llvm2smt/src/{llvm2smt,dltest,parse,rawparse} /usr/local/bin'

# Any arguments provided in
#	docker run llvm2smt $@
# will be passed to llvm2smt
ENTRYPOINT ["llvm2smt"]
