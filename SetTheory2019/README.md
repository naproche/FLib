# Set Theory


---

- **Authors:** Alexander Holz (2019), Marcel Schütz (2019)

- **Required Naproche version:** [Isabelle/Naproche 2019][1]

- **Required amount of free memory:** ~ 600 MB

- **Approximate verification time:** ~ 30 min

- **Verified with:** [E 2.0][2]

---


This is an approach on formalizing the [script][3] of an introductory lecture on
set theory held by Peter Koepke in the winter term 2018/19 at the University of
Bonn.


## Contents

The formalization covers the following sections of the script.

 2. The ZF Axioms

 3. Ordinal numbers

 8. Cardinalities

 9. Finite, countable and uncountable sets

10. The alephs

11. Cardinal arithmetic

12. Wellfounded relations

13. Further cardinal arithmetic

14. Cofinality


## How to read the formalization

Informal parts of the script are commented in the formalization with one single
`#`-character. In contrast to that, technical notes on the formalization that do
not stem from the script are commented with two `#`-characters. Moreover, parts
of the formalization that can not be found in the script are enclosed within
`## >>>>>>>` and `## <<<<<<<`. Example:

```
# For disjoint finite sets a and b natural addition and multiplication satisfies
# card(a \cup b) = card(a) + card(b) and card(a \times b) =
# card(a) \cdot card(b). This motivates the following extension of natural
# arithmetic to all cardinals.

Definition 99_a. kappa \plus mu = card((kappa \times ZERO) \cup (mu \times ONE)).

Definition 99_b. kappa \cdot mu = card(kappa \times mu).

Definition 99_c. kappa^mu = card(^{mu}{kappa}).

## Note that we cannot use "+" to denote cardinal addition since "+" is already
## used in the "+ 1" operation on arbitrary sets.


## >>>>>>>

  Lemma. kappa \plus mu is a cardinal.

  Lemma. kappa \cdot mu is a cardinal.

  Lemma. kappa^mu is a cardinal.

## <<<<<<<
```

The first four lines are comments that can be found literally in the script and
do not provide any formal content which could be adopted to the formalization
(indicated with `#`). The lines afterwards are formalizations of definitions as
they appear in the script. Then a technical comment is made about these
definitions which is _not_ part of the script (indicated with `##`). After that
some lemmas are added to the formalization wich also do not appear in the script
(enclosed within `## >>>>>>>` and `## <<<<<<<`).



[1]: <https://sketis.net/2019/isabelle-naproche-for-automatic-proof-checking-of-ordinary-mathematical-texts>
[2]: <http://wwwlehre.dhbw-stuttgart.de/~sschulz/E/Archive.html>
[3]: <http://www.math.uni-bonn.de/ag/logik/teaching/2018WS/set_theory/current_scriptum.pdf>
