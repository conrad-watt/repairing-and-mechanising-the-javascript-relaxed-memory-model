# Mixed-sized JS memory model and proofs about it

This repository contains a part of the Coq code supplementing the paper
*Repairing and Mechanising the JavaScript Relaxed Memory Model*
by Conrad Watt, Christopher Pulte, Anton Podkopaev, Guillaume Barbier, Stephen Dolan, Shaked Flur, Jean Pichon-Pharabod, and Shu-yu Guo.
The other part (uni-sized JS memory model and compilation to IMM) is located in [the IMM repo](https://github.com/weakmemory/imm).

## Building the Project

### Requirements
* [Coq 8.9.1](https://coq.inria.fr)
* [Hahn library](https://github.com/vafeiadis/hahn) (`coq-hahn`)
* [The Coq development of IMM](https://github.com/weakmemory/imm) (`coq-imm`)

### Building Manually

To build the project, one needs to install some libraries (`hahn` and `imm`), which the project
depends on. This might be done by running `./configure`.
The command installs `Coq` as well. After that, one needs to run `make` (or `make -j4` for a faster build).

## Description of code and its relation to the paper
The build process has been tested on Coq version 8.9.1.

The mixed-size ARMv8 and proofs are in the imm/src/arm_mixed sub-directory

The JavaScript model (stylized as "JSMM") and proofs are in the imm/src/jsmm sub-directory

named lemmas in the paper are named identically in the mechanisation

in particular,

internal_sc_drf : coq/imm/src/jsmm_mixed/JSMM_m_scdrf.v :: line 57

jsmm_compilation : coq/imm/src/arm_mixed/JSMM_m_ToArm_mixed.v :: line 962

The lemma s_imm_consistent_implies_jsmm_consistent has been integrated into the core IMM project and can be found there (https://github.com/weakmemory/imm/blob/master/src/jsmm/JSMMToimm_s.v)
