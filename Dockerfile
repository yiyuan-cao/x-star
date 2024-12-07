FROM ocaml/opam:debian-12-ocaml-4.14

# Install System Packages
USER root
RUN sudo apt-get update && sudo apt-get upgrade -y
RUN sudo apt-get install -y make gcc clang git m4 pkg-config libgc-dev libgmp-dev
USER opam

# Install opam packages
RUN opam install --yes zarith ocamlfind camlp5.8.02.01 dune \
    ppx_jane core core_unix pprint ppx_deriving menhir \
    async csv ppx_import yojson ppx_yojson_conv lsp

# Install Rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/home/opam/.cargo/bin:${PATH}"
RUN rustup default stable && cargo install cbindgen

# Install dmtcp
WORKDIR /home/opam
RUN git clone https://github.com/dmtcp/dmtcp.git
WORKDIR /home/opam/dmtcp
RUN ./configure && make -j && sudo make install

# Shell environment
WORKDIR /home/opam
ENTRYPOINT ["opam", "exec", "--"]
CMD ["/bin/bash", "--login"]
