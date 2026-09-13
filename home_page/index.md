---
layout: default
usemathjax: true
---

**rocq-dynamics** is a Rocq / MathComp port of the Lean 4 + Mathlib monorepo
[leanamycs](https://github.com/formal-dynamics/leanamycs): complete,
`Admitted`-free formalizations of two classical results on opinion dynamics
on the complete graph, built on a minimal finite-probability layer (uniform
averages over finite types, no measure theory) and a self-contained Chernoff
bound.

## Rumor spreading (uniform push)

In the *push* model on $K_n$, every informed node sends the rumor to a
uniformly random other node each round. Starting from a single informed node,
after $(\lceil 117 \ln n\rceil + 23) + \lceil 6 \ln n\rceil$ rounds **all**
nodes are informed with probability at least $1 - 2/n$. Main theorem:
`Dynamics.rumor.main.push_informs_all_whp`.

## 3-majority dynamics

Each of $n$ agents holds one of two opinions and, every round, adopts the
majority opinion among three agents sampled uniformly at random. From an
initial majority of at least $60\%$ and for $\ln n \ge 30$, after
$10 + (\lceil 6 \ln n\rceil + 2)$ rounds **all** agents hold the majority
opinion with probability at least $1 - 500/n$. Main theorem:
`Dynamics.majority.main.majority3_consensus_whp`.

## Links

* [Blueprint]({{ '/blueprint/' | relative_url }}) · [as pdf]({{ '/blueprint.pdf' | relative_url }}) ·
  [dependency graph]({{ '/blueprint/dep_graph_document.html' | relative_url }})
* [API documentation (coqdoc)]({{ '/docs/toc.html' | relative_url }})
* [Source](https://github.com/formal-dynamics/rocq-dynamics) ·
  [Lean original](https://github.com/formal-dynamics/leanamycs)

Both main theorems depend only on the three classical axioms of
mathcomp-classical (`boolp`); `verify.sh` in the repository audits this on
every build.
