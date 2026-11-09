# Hurwitz's squares problem, in plain language

*A non-technical explanation of the research note in this folder. The [note](note.md) is the precise statement; this page only tries to say what it is about.*

## A puzzle about multiplying sums of squares

Take two numbers that are each a sum of two squares, say $1^2+2^2=5$ and $3^2+4^2=25$. Their product, $125$, is again a sum of two squares:

$$(a^2+b^2)(c^2+d^2)=(ac-bd)^2+(ad+bc)^2$$

With $a,b=1,2$ and $c,d=3,4$ the right-hand side is $(-5)^2+10^2=25+100=125$. So a product of two sums of 2 squares needs only 2 new squares, not the 4 you get by multiplying everything out.

The same trick works for sums of 4 squares (Euler) and 8 squares (Degen). Hurwitz proved in 1898 that it works *exactly* only for $N=1,2,4,8$.

## The question

Now allow some slack. For $N$ squares times $N$ squares:

$$(x_1^2+\dots+x_N^2)(y_1^2+\dots+y_N^2)=\ ?$$

How many squares (or products of two simple expressions) do you need on the right-hand side?

- Multiplying everything out always works and uses $N^2$.
- For $N=2,4,8$ the neat identities use only $N$.
- For other $N$, nobody knows how low the count can go. Writing it as $N^e$, the exponent $e$ is at most $2$ trivially and, until now, the best known value was about $1.615$ (Hrubeš, 2024).

(The precise quantity in the note is a closely related one, equal to the above up to a constant factor. See the note for the exact definitions.)

## What the note adds

The note claims that $e=\sqrt2\approx1.414$ is enough, for very large $N$. If correct, this narrows the range in which the true answer can lie from $[1,\,1.615]$ to $[1,\,1.414]$. It does not say whether the true answer is closer to $1$ or to $1.414$.

## Where it comes from

In October 2026 an AI model (Claude) published a fast algorithm for a hard computing problem (3-SAT). Inside it is a construction that cuts a "crossing" of two wires into pieces so that each piece is simple. The authors noticed that this cutting is the same thing as Hurwitz's puzzle, but, as far as I can see, only worked out the weaker case, which gives $e=11/6\approx1.83$. The note applies the same remark to their stronger construction, which gives $\sqrt2$.

## What this is not

- **Not a result about P vs NP.** Nothing here bears on it.
- **Not useful in practice.** The bound only wins for astronomically large $N$. The "$+o(1)$" in $N^{\sqrt2+o(1)}$ fades very slowly. Computing the effective exponent for $N=2^\lambda$ gives:

| $\lambda$ | 20 | 60 | 80 | 120 | 600 |
|---|---|---|---|---|---|
| effective exponent | 1.92 | 1.64 | 1.60 | 1.55 | 1.45 |

  It overtakes the 2024 record only around $N\approx2^{70}$.
- **Not confirmed.** It rests on a theorem in the ETH paper whose proof the authors checked with AI and Lean, but which no human expert has yet verified independently. Nobody has confirmed that the observation is new.

## Who did what

The mathematics was produced by AI models (Claude Sonnet 5.5 and Claude Fable 5.1) in sessions directed by Jakub Piotr Siemaszko, who is not a mathematician and cannot judge the argument himself. What he did check: the two scripts run and print the numbers the note reports. One script verifies the whole construction exactly in the two smallest cases ($N=4$ with 307 products, and $N=8$ with 1508 products). The other computes the table above.

If you can tell that something here is wrong, already known, or worth following up, please open an issue.
