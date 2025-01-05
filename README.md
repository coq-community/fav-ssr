<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Functional Data Structures and Algorithms in SSReflect

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/coq-community/fav-ssr/actions/workflows/docker-action.yml/badge.svg?branch=trunk
[docker-action-link]: https://github.com/coq-community/fav-ssr/actions/workflows/docker-action.yml

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



A port of the book https://functional-algorithms-verified.org/ to Coq/SSReflect.

The book was previously called "Functional Algorithms Verified", hence the FAV acronym.

## Meta

- Author(s):
  - Alex Gryzlov (initial)
- Coq-community maintainer(s):
  - Alex Gryzlov ([**@clayrat**](https://github.com/clayrat))
- License: [MIT license](LICENSE)
- Compatible Coq versions: 8.16 to 8.20
- Additional dependencies:
  - [MathComp ssreflect](https://math-comp.github.io) 2.2 to 2.3
  - [MathComp algebra](https://math-comp.github.io)
  - [Equations](https://github.com/mattam82/Coq-Equations) 1.3 or later
- Coq namespace: `favssr`
- Related publication(s): none

## Building instructions

To build manually, do:
```shell
make   # or make -j <number-of-cores-on-your-machine>
```

## Contents

1. [Basics](src/basics.v)
### Part I: Sorting and Selection
2. [Sorting](src/sorting.v)
3. [Selection](src/selection.v)
### Part II: Search Trees
4. [Binary Trees](src/bintree.v)
5. [Binary Search Trees](src/bst.v)
6. [Abstract Data Types](src/adt.v)
7. [2-3 Trees](src/twothree.v)
8. [Red-Black Trees](src/redblack.v)
9. [AVL Trees](src/avl.v)
10. [Beyond Insert and Delete: \cup, \cap and -](src/beyond.v)
11. [Arrays via Braun Trees](src/braun.v)
12. [Tries](src/trie.v)
13. [Region Quadtrees](src/quadtree.v)
### Part III: Priority Queues
14. [Priority Queues](src/priority.v)
15. [Leftist Heaps](src/leftist.v)
16. [Priority Queues via Braun Trees](src/braun_queue.v)
17. [Binomial Heaps](src/binom_heap.v)
### Part IV: Advanced Design and Analysis Techniques
18. Dynamic Programming
19. Amortized Analysis
20. Queues
21. Splay Trees
22. Skew Heaps
23. Pairing Heaps
### Part V: Selected Topics
24. Knuth–Morris–Pratt String Search
25. [Huffman’s Algorithm](src/huffman.v)
26. Alpha-Beta Pruning
