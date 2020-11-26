# 4 The symmetric difference

[read FLib/Statements/Library/SetTheory/03_computation-laws.ftl]


Let x,y,z denote zets.


# Definition

Definition 0401. x /triangle y  = (x /cup y) /setminus (x /cap y).


# Computation laws

Proposition 0402. x /triangle y = (x /setminus y) /cup (y /setminus x).

Proof.
  x /triangle y /subseteq (x /setminus y) /cup (y /setminus x).
  proof.
    Let u /in x /triangle y. Then u /in x /cup y and u /notin x /cap y. Hence
    (u /in x or u /in y) and not (u /in x and u /in y). Thus (u /in x or
    u /in y) and (u /notin x or u /notin y). Therefore if u /in x then
    u /notin y. if u /in y then u /notin x. Then we have (u /in x and
    u /notin y) or (u /in y and u /notin x). Hence u /in x /setminus y or
    u /in y /setminus x. Thus u /in (x /setminus y) /cup (y /setminus x).
  end.

  (x /setminus y) /cup (y /setminus x) /subseteq x /triangle y.
  proof.
    Let u /in (x /setminus y) /cup (y /setminus x). Then (u /in x and
    u /notin y) or (u /in y and u /notin x). If u /in x and u /notin y then
    u /in x /cup y and u /notin x /cap y. If u /in y and u /notin x then
    u /in x /cup y and u /notin x /cap y. Hence u /in x /cup y and
    u /notin x /cap y. Thus u /in (x /cup y) /setminus (x /cap y) =
    x /triangle y.
  end.
qed.


Proposition 0403. x /triangle y = y /triangle x.

Proof.
  x /triangle y = (x /cup y) /setminus (x /cap y) = (y /cup x) /setminus
  (y /cap x) = y /triangle x.
qed.


Proposition 0404. (x /triangle y) /triangle z = x /triangle (y /triangle z).

Proof.
  We have x /triangle y = (x /setminus y) /cup (y /setminus x). Hence
  (x /triangle y) /triangle z = (((x /setminus y) /cup (y /setminus x))
  /setminus z) /cup (z /setminus ((x /setminus y) /cup (y /setminus x))).

  we have y /triangle z = (y /setminus z) /cup (z /setminus y). Hence
  x /triangle (y /triangle z) = (x /setminus ((y /setminus z) /cup
  (z /setminus y))) /cup (((y /setminus z) /cup (z /setminus y)) /setminus x).

  (((x /setminus y) /cup (y /setminus x)) /setminus z) /cup
  (z /setminus ((x /setminus y) /cup (y /setminus x))) /subseteq
  (x /setminus ((y /setminus z) /cup (z /setminus y))) /cup (((y /setminus z)
  /cup (z /setminus y)) /setminus x).
  proof.
    Let u /in (((x /setminus y) /cup (y /setminus x)) /setminus z) /cup
    (z /setminus ((x /setminus y) /cup (y /setminus x))).

    Case u /in ((x /setminus y) /cup (y /setminus x)) /setminus z.
      Then u /notin z.

      Case u /in x /setminus y.
        Then u /notin y /setminus z and u /notin z /setminus y.
        u /in x. Hence u /in x /setminus ((y /setminus z) /cup (z /setminus y)).
        Thus u /in (x /setminus ((y /setminus z) /cup (z /setminus y))) /cup
        (((y /setminus z) /cup (z /setminus y)) /setminus x). 
      end.

      Case u /in y /setminus x.
        Then u /in y /setminus z. Hence u /in (y /setminus z) /cup
        (z /setminus y). u /notin x. Thus u /in ((y /setminus z) /cup
        (z /setminus y)) /setminus x. Therefore u /in (x /setminus
        ((y /setminus z) /cup (z /setminus y))) /cup (((y /setminus z) /cup
        (z /setminus y)) /setminus x).
      end.
    end.

    Case u /in z /setminus ((x /setminus y) /cup (y /setminus x)).
      Then u /in z. u /notin x /setminus y and u /notin y /setminus x.
      Hence not (u /in x /setminus y or u /in y /setminus x). Thus not
      ((u /in x and u /notin y) or (u /in y and u /notin x)). Therefore
      (u /notin x or u /in y) and (u /notin y or u /in x).

      Case u /in x.
        Then u /in y. Hence u /notin (y /setminus z) /cup (z /setminus y). Thus
        u /in x /setminus ((y /setminus z) /cup (z /setminus y)). Therefore
        u /in (x /setminus ((y /setminus z) /cup (z /setminus y))) /cup
        (((y /setminus z) /cup (z /setminus y)) /setminus x).
      end.

      Case u /notin x.
        Then u /notin y. Hence u /in z /setminus y. Thus u /in (y /setminus z)
        /cup (z /setminus y). Therefore u /in ((y /setminus z) /cup
        (z /setminus y)) /setminus x. Then we have u /in (x /setminus
        ((y /setminus z) /cup (z /setminus y))) /cup (((y /setminus z) /cup
        (z /setminus y)) /setminus x).
      end.
    end.
  end.

  (x /setminus ((y /setminus z) /cup (z /setminus y))) /cup
  (((y /setminus z) /cup (z /setminus y)) /setminus x) /subseteq
  (((x /setminus y) /cup (y /setminus x)) /setminus z) /cup (z /setminus
  ((x /setminus y) /cup (y /setminus x))).
  proof.
    Let u /in (x /setminus ((y /setminus z) /cup (z /setminus y))) /cup
    (((y /setminus z) /cup (z /setminus y)) /setminus x).

    Case u /in x /setminus ((y /setminus z) /cup (z /setminus y)).
      Then u /in x. u /notin y /setminus z and u /notin z /setminus y.
      Hence not (u /in y /setminus z or u /in z /setminus y). Thus not
      ((u /in y and u /notin z) or (u /in z and u /notin y)). Therefore
      (u /notin y or u /in z) and (u /notin z or u /in y).

      Case u /in y.
        Then u /in z. u /notin x /setminus y and
        u /notin y /setminus x. Hence u /notin (x /setminus y) /cup
        (y /setminus x). Thus u /in z /setminus ((x /setminus y) /cup
        (y /setminus x)). Therefore u /in (((x /setminus y) /cup
        (y /setminus x)) /setminus z) /cup (z /setminus ((x /setminus y) /cup
        (y /setminus x))).
      end.

      Case u /notin y.
        Then u /notin z. u /in x /setminus y. Hence
        u /in (x /setminus y) /cup (y /setminus x). Thus u /in ((x /setminus y)
        /cup (y /setminus x)) /setminus z. Therefore u /in (((x /setminus y)
        /cup (y /setminus x)) /setminus z) /cup (z /setminus ((x /setminus y)
        /cup (y /setminus x))).
      end.
    end.

    Case u /in ((y /setminus z) /cup (z /setminus y)) /setminus x.
      Then u /notin x.

      Case u /in y /setminus z.
        Then u /in y /setminus x. Hence u /in (x /setminus y) /cup
        (y /setminus x). Thus u /in ((x /setminus y) /cup (y /setminus x))
        /setminus z. Therefore u /in (((x /setminus y) /cup (y /setminus x))
        /setminus z) /cup (z /setminus ((x /setminus y) /cup (y /setminus x))).
      end.

      Case u /in z /setminus y.
        Then u /in z. u /notin x /setminus y and
        u /notin y /setminus x. Hence u /notin (x /setminus y) /cup
        (y /setminus x). Thus u /in z /setminus ((x /setminus y) /cup
        (y /setminus x)). Therefore u /in (((x /setminus y) /cup
        (y /setminus x)) /setminus z) /cup (z /setminus ((x /setminus y) /cup
        (y /setminus x))).
      end.
    end.
  end.
qed.


Proposition 0405. x /cap (y /triangle z) = (x /cap y) /triangle (x /cap z).

Proof.
  x /cap (y /triangle z) = x /cap ((y /setminus z) /cup (z /setminus y)) =
  (x /cap (y /setminus z)) /cup (x /cap (z /setminus y)).

  x /cap (y /setminus z) = (x /cap y) /setminus (x /cap z).
  x /cap (z /setminus y) = (x /cap z) /setminus (x /cap y).

  Hence x /cap (y /triangle z) = ((x /cap y) /setminus (x /cap z)) /cup
  ((x /cap z) /setminus (x /cap y)) = (x /cap y) /triangle (x /cap z).
qed.


Proposition 0406. x /subseteq y iff x /triangle y = y /setminus x.

Proof.
  If x /subseteq y then x /triangle y = y /setminus x.
  proof.
    Assume x /subseteq y. Then x /cup y = y and x /cap y = x. Hence the thesis.
  end.

  If x /triangle y = y /setminus x then x /subseteq y.
  proof.
    Assume x /triangle y = y /setminus x. Let u /in x. Then
    u /notin y /setminus x. Hence u /notin x /triangle y. Thus u /notin x /cup y
    or u /in x /cap y. Indeed x /triangle y = (x /cup y) /setminus (x /cap y).
    If u /notin x /cup y then we have a contradiction. Therefore u /in x /cap y.
    Then we have the thesis.
  end.
qed.


Proposition 0407. x /triangle y = x /triangle z iff y = z.

Proof.
  If x /triangle y = x /triangle z then y = z.
  proof.
    Assume x /triangle y = x /triangle z.

    y /subseteq z.
    proof.
      Let u /in y.

      Case u /in x.
        Then u /notin x /triangle y. Hence u /notin x /triangle z. Therefore
        u /in x /cap z. Indeed x /triangle z = (x /cup z) /setminus (x /cap z).
        Hence u /in z.
      end.

      Case u /notin x.
        Then u /in x /triangle y. Indeed u /in x /cup y and u /notin x /cap y.
        Hence u /in x /triangle z. Thus u /in x /cup z and u /notin x /cap z.
        Therefore u /in x or u /in z. Then we have the thesis.
      end.
    end.

    z /subseteq y.
    proof.
      Let u /in z.

      Case u /in x.
        Then u /notin x /triangle z. Hence u /notin x /triangle y. Therefore
        u /in x /cap y. Indeed u /notin x /cup y or u /in x /cap y. Hence
        u /in y.
      end.

      Case u /notin x.
        Then u /in x /triangle z. Indeed u /in x /cup z and u /notin x /cap z.
        Hence u /in x /triangle y. Thus u /in x /cup y and u /notin x /cap y.
        Therefore u /in x or u /in y. Then we have the thesis.
      end.
    end.
  end.
qed.


Proposition 0408. x /triangle x = /emptyset.

Proof.
  x /triangle x = (x /cup x) /setminus (x /cap x) = x /setminus x = /emptyset.
qed.


Proposition 0409. x /triangle /emptyset = x.

Proof.
  x /triangle /emptyset = (x /cup /emptyset) /setminus (x /cap /emptyset) =
  x /setminus /emptyset = x.
qed.


Proposition 0410. x = y iff x /triangle y is empty.

Proof.
  If x = y then x /triangle y is empty.
  proof.
    Assume x = y. Then x /triangle y = (x /cup x) /setminus (x /cap x) =
    x /setminus x = /emptyset. Hence the thesis.
  end.

  If x /triangle y is empty then x = y.
  proof.
    Assume that x /triangle y is empty. Then (x /cup y) /setminus (x /cap y) is
    empty. Hence every element of x /cup y is an element of x /cap y. Thus for
    all objects u if u /in x or u /in y then u /in x and u /in y. Therefore
    every element of x is an element of y. every element of y is an
    element of x. Then we have the thesis.
  end.
qed.
