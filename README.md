# Planar Rook Algebras

[![Lean Action CI](https://github.com/rspencer01/planar_rooks/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/rspencer01/planar_rooks/actions/workflows/lean_action_ci.yml)
[![Documentation](https://img.shields.io/badge/documentation-github.io-blue)](https://rspencer01.github.io/planar_rooks/docs)

This repository contains a very rough and incredibly verbose attempt to derive a theory of the representation theory of Planar Rook Algebras.

For an introduction see [[FHH08]](https://arxiv.org/pdf/0806.3960). The representation theory link to algebraic groups (outside scope but motivating) can be read in [[BM12]](https://arxiv.org/pdf/1201.2482) and homological motivation (also outside scope) can be found in [[Kho12]](https://arxiv.org/pdf/1101.0293).

This project will aim to show the cellularity of the algebras and that their representation theory depends only on whether δ is nonzero.

### Why are the proofs so terrible
I am not an experienced LEAN user (am just picking it up again after several years' hiatus) and don't care much about making my proofs fast or neat.

Simplification PRs are welcome.

### Progress
This is an incomplete list of things that need to be done.

#### Planar Rook Monoid
 * [x] Definition of diagrams
 * [x] Definition of monoid
 * [ ] Cardinality of monoid
 * [x] Counting loose strands
 * [ ] Cardinality of epi and mono elements
 * [x] The involution

#### Planar Rook Algebra
 * [x] Definition
 * [ ] The involution
 * [x] Independence on the parameter

#### Cellular Algebras
 * [x] Defintions of cellular algebras 
 * [ ] Structure of cellular algebras
 * [ ] Statements of results in cellular algebras

#### Representation theory of Planar Rook Algebras
 * [ ] Proof of cellularity
 * [ ] Dimensions of cell modules
 * [ ] Irreducibility of cell modules if parameter doesn't vanish