FROM ubuntu:16.04

MAINTAINER Pierre-Yves Strub <pierre-yves@strub.nu>

ENV DEBIAN_FRONTEND noninteractive

RUN \
	set -e; \
	apt-get -q -y update; \
	apt-get -q -y dist-upgrade; \
	apt-get -q -y install sudo m4 rsync git python; \
	apt-get -q -y --no-install-recommends install ocaml-nox opam aspcud; \
	apt-get -q -y clean

COPY sudo-ci /etc/sudoers.d/ci

RUN adduser --disabled-password --gecos "CI" ci
RUN chmod 440 /etc/sudoers.d/ci

USER    ci
WORKDIR /home/ci

ENV OPAMYES     true
ENV OPAMVERBOSE 0
ENV OPAMJOBS    2

RUN \
	set -e; \
	opam init -a; \
	opam remote add coq-released  https://coq.inria.fr/opam/released; \
	opam remote add coq-core-dev  https://coq.inria.fr/opam/core-dev; \
	opam remote add coq-extra-dev https://coq.inria.fr/opam/extra-dev

ARG COQVERSION
ARG SSRVERSION
ARG SSRPACKAGES

RUN \
	set -e; \
	opam pin add -n coq ${COQVERSION} && opam install coq; \
	if [ ${SSRVERSION} != "dev" ]; then \
	  opam pin add -n coq-mathcomp-ssreflect ${SSRVERSION}; \
	fi; \
	opam install coq-mathcomp-ssreflect.${SSRVERSION}; \
	opam install ${SSRPACKAGES}; \
	rm -rf .opam/packages.dev/* .opam/system/packages.dev/*; \
	rm -rf .opam/system/build/* .opam/archives/*
