# fufp-growth
A (slightly modified) version of the Fast-Updated FP-growth algorithm implemented in Python.

The FUFP-growth algorithm was described by TP Hong et al. on [1], which provides a mechanism to improve the performance of standard FP-growth. It allows frequent updates to the constructed FP-tree thereby allowing it to be efficiently reconstructed for new transactions.

This module is an implementation of this FUFP-growth algorithm, with minor modififcations.

Uses enaeseth's python-fp-growth module [2] for the FP-tree construction logic.

[1] http://dl.acm.org/citation.cfm?id=1342423.1342599

[2] https://github.com/enaeseth/python-fp-growth
