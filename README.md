---
date: 2026-07-17
name: A proof of a generalisation of Conjecture 314 from Written on the Wall II
---

With the help of a clanker, I found a [Lean proof](https://github.com/glyaea/wow-ii-314/blob/7b35f1252e4aaae3c787faf8091f9c7cd4edc41f/solution.lean) of the [DeepMind formalisation](https://google-deepmind.github.io/formal-conjectures/theorem/?name=WrittenOnTheWallII.GraphConjecture314.conjecture314) of Conjecture 314 from [Written on the Wall II](http://cms.dt.uh.edu/faculty/delavinae/research/wowII).
Here, I prove a generalisation of the conjecture.

---

Consider finite simple graphs.

> **Claim 1**. Each connected, K3-free, induced-P5-free graph is well-totally-dominated.

Fix such a graph.

> **Lemma**. Each node $m$ of a minimal total dominating set $M$ has a neighbour $n$ in $M$.

> **Lemma**. Each node $m$ of a minimal total dominating set $M$ has a private neighbour that only $m$ in $M$ is connected to.

> **Lemma**. A node is reachable from any other in $3$ or fewer hops.

> **Lemma**. A minimal total dominating set of size $3$ forms a chain.

> **Claim 1.1**. No minimal total dominating set can have $1$ node or fewer.

This is immediate.

> **Claim 1.2**. No minimal total dominating set can have $4$ nodes or more.

For a minimal total dominating set with at least $4$ nodes, there are 2 cases:
- **Case 1**. The nodes are connected.
- **Case 2**. The nodes are disconnected.

For Case 1, if a node $n$ has $3$ or more neighbours among the nodes, then $n$ and $3$ of its neighbours form a star, since the neighbours cannot pair with each other.
Otherwise, the nodes form a line or a cycle.
Thus, for Case 1, there are 3 cases:
- **Case 1.1**. $4$ of the nodes form a line.
- **Case 1.2**. $4$ of the nodes form a star.
- **Case 1.3**. $4$ of the nodes form a cycle.

For Case 1.1:
```
A - B - C - D
```
`D` has a private neighbour:
```
A - B - C - D - e
```
This is an induced P5, which is banned.

For Case 1.2:
```
B
|
A - C
|
D
```
Since `B` has a private neighbour, and `D` has a private neighbour:
```
x
|
B
|
A - C
|
D
|
y
```
If `x` pairs with `y`:
```
x ----
|     |
B     |
|     |
A - C |
|     |
D     |
|     |
y ----
```
`x - y - D - A - C` is an induced P5, which is banned.
Else, `x - B - A - D - y` is an induced P5, which is banned.

For Case 1.3:
```
B - A
|   |
D - C
```
Since `A` has a private neighbour `x`, `B` has a private neighbour `y`, and `D` has a private neighbour `z`:
```
y
|
B - A - x
|   |
D - C
|
z
```
If `x` pairs with `z`, and `y` pairs with `x`:
```
y ------
|       |
B - A - x
|   |   |
D - C   |
|       |
z ------
```
`y - x - z - D - C` is an induced P5, which is banned.
Else if `x` pairs with `z`, and `y` pairs with `z`:
```
y --------
|         |
B - A - x |
|   |   | |
D - C   | |
|       | |
z ------  |
|         |
 ---------
```
`y - z - x - A - C` is an induced P5, which is banned.
Else if `x` pairs with `z`:
```
y
|
B - A - x
|   |   |
D - C   |
|       |
z ------
```
`y - B - A - x - z` is an induced P5, which is banned.
Else, `x - A - B - D - z` is an induced P5, which is banned.

For Case 2, the nodes must contain $2$ disconnected pairs:
```
A - B   C - D
```
Without loss of generality, consider the distance from `A` to `C`.
If the distance is $2$ hops:
```
B - A - X - C - D
```
This is an induced P5, which is banned.
If the distance is $3$ hops:
```
B - A - X - Y - C - D
```
If `B` pairs with `Y`:
```
B - A - X - Y - C - D
|           |
 -----------
```
`A - B - Y - C - D` is an induced P5, which is banned.
Else, `B - A - X - Y - C` is an induced P5, which is banned.

> **Claim 1.3**. Minimal total dominating sets of sizes $2$ and $3$ cannot coexist.

Let `U - V` be a minimal total dominating set of size $2$, and `A - B - C` be a minimal total dominating set of size $3$.
Since `A` has a private neighbour and `C` has a private neighbour:
```
p - A - B - C - q
```
Without loss of generality, assume `A` pairs with `U`:
```
p - A - B - C - q
    |
    U
```
Since `p` must connect with `U - V`, `p` must pair with `V`:
```
p - A - B - C - q
|   |
V - U
```
Since `B` must connect with `U - V`, `B` must pair with `V`:
```
           ---------
          |         |
  p - A - B - C - q |
  |   |             |
  V - U             |
 /                  |
|                   |
 -------------------
```
Since `C` must connect with `U - V`, `C` must pair with `U`:
```
           ---------
          |         |
  p - A - B - C - q |
  |   |       |     |
  V - U ------      |
 /                  |
|                   |
 -------------------
```
Since `q` must connect with `U - V`, `q` must pair with `V`:
```
           ---------
          |         |
  p - A - B - C - q |
  |   |       |   | |
  V - U ------    | |
 / \              | |
|   --------------  |
 -------------------
```
`p - A - B - C - q` is an induced P5, which is banned.

Notably, Claim 1 can be generalised to disconnected graphs.

> **Claim 2**. Each K3-free, induced-P5-free graph is well-totally-dominated.

Fix such a graph of $k$ connected components.
Let $D$ be a minimal total dominating set.

> **Lemma**. For each connected component $C$, $D$ has a minimal total dominating set of $C$.

So $D$ locally decomposes as:

$$
	D=D_{1}\sqcup D_{2}\sqcup\dots\sqcup D_{k}
$$

This gives:

$$
	|D|=|D_{1}|+|D_{2}|+\cdots+|D_{k}|
$$

Since each summand is constant, the sum is constant.
