# Lean Doodles

Casual notes in [Lean](https://lean-lang.org): proofs of various theorems not tied to any specific project.

## May's Theorem

[`MaysTheorem.lean`](/LeanDoodles/MaysTheorem.lean)

May's theorem states that majority rule is the only reasonable (near decisive, anonymous, neutral, and monotone) voting system for two candidates.

You can learn more about it on [my blog](https://dobranow.ski/posts/mays-theorem) or [Wikipedia](https://en.wikipedia.org/wiki/May%27s_theorem).

## Number Pairs

[`NumberPairs.lean`](/LeanDoodles/NumberPairs.lean)

A *Number Pair* for a given $d \in \mathbb{N}$ is a pair of numbers $(a, b)$ such that $b - a = d$ and the sum of the digits of $a$ is equal to the sum of the digits of $b$.

This module contains a constructive proof that a Number Pair exists if and only if $d$ is divisible by $9$.

Inspired by the Wincent DragonByte 2025, [problem N](https://www.wincentdragonbyte.com/archive/qual2025/N/statement) from the qualification round.
