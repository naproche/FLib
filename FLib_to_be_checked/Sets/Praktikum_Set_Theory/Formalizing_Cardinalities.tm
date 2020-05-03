<TeXmacs|1.99.8>

<style|<tuple|generic|german>>

<\body>
  <doc-data|<doc-title|Beginning to formalize a chapter on cardinals>>

  We want to faithfully formalize the first lines of a chapter from a set
  theory scriptum in ForTheL so that it is accepted in the Naproche-SAD
  system. Since we concentrate on this chapter, earlier material can simply
  be \Rimported\P as signature extensions with axioms, instead of
  constructing that material and proving its properties.

  <with|font-base-size|9|<\quote-env>
    <section|Cardinalities>

    Apart from its foundational role, set theory is mainly concerned with the
    study of arbitrary infinite sets and in particular with the question of
    their size. Cantor's approach to infinite sizes follows naive intuitions
    familiar from finite sets of objects.

    <\definition>
      \;

      <\enumerate-alpha>
        <item><math|x> and <math|y> are <em|equipollent>, or <em|equipotent>,
        or have <em|the same cardinality>, written <math|x\<sim\>y>, if
        <math|\<exists\>f f:x\<leftrightarrow\>y >.

        <item><math|x> has <em|cardinality at most that of ><math|y>, written
        <math|x\<preccurlyeq\>y>, if <math|\<exists\>f
        f:x\<rightarrow\>y<with|mode|text| is injective>>.

        <item>We write <math|x\<prec\>y> for <math|x\<preccurlyeq\>y> and
        <math|x\<nsim\>y >.
      </enumerate-alpha>
    </definition>

    These relations are easily shown to satisfy

    <\lemma>
      Assume <math|ZF>. Then

      <\enumerate-alpha>
        <item><math|\<sim\>> is an equivalence relation on <math|V>.

        <item><math|x\<sim\>y \<rightarrow\> x\<preccurlyeq\>y \<wedge\>
        y\<preccurlyeq\>x >.

        <item><math|x\<preccurlyeq\>x >.

        <item><math|x\<preccurlyeq\>y \<wedge\> y\<preccurlyeq\>z
        \<rightarrow\> x\<preccurlyeq\>z >.

        <item><math|x\<subseteq\>y \<rightarrow\> x\<preccurlyeq\>y >.
      </enumerate-alpha>
    </lemma>

    <text-dots> <text-dots>
  </quote-env>>

  We begin like this:

  <verbatim|<\quote-env>
    # 8 Cardinalities

    \;

    Definition 77a. x ~ y iff exists f f : x \<less\>-\<gtr\> y.

    Let x and y are equipollent stand for x ~ y.

    Let x and y have same cardinality stand for x ~ y.

    \;

    Definition 77b. x \\preccurlyeq y iff there exists f such that f : x
    -\<gtr\> y and f is injective.

    \;

    # Definition 77c.

    Let x \\preccurly y stand for x \\preccurlyeq y and not x~ y.
  </quote-env>>

  This throws various errors:

  <\itemize-minus>
    <item>types of variables are not fixed, hence the variables are not
    accepted;

    <item>relations like the ternary <verbatim|f : x \<less\>-\<gtr\> y> are
    not defined.
  </itemize-minus>

  To fix this we introduce appropriate language extensions
  (<verbatim|Signature>):

  <verbatim|<\quote-env>
    # Preliminaries

    Let x,y denote sets.

    Let f denote functions.

    \;

    Signature. f : x -\<gtr\> y is an atom.

    Signature. f : x \<less\>-\<gtr\> y is an atom.

    Signature. f is injective is an atom.

    \;

    # 8 Cardinalities

    \;

    Definition 77a. x ~ y iff exists f f : x \<less\>-\<gtr\> y.

    Let x and y are equipollent stand for x ~ y.

    Let x and y have same cardinality stand for x ~ y.

    \;

    Definition 77b. x \\preccurlyeq y iff there exists f such that f : x
    -\<gtr\> y and f is injective.

    \;

    # Definition 77c.

    Let x \\preccurly y stand for x \\preccurlyeq y and not x~ y.
  </quote-env>>

  Notes:

  <\itemize-minus>
    <item>We use the inbuilt notions of <verbatim|sets> and
    <verbatim|functions>;

    <item>the signature extensions provide notations for predicates that
    suggest their ordinary mathematical meanings; strictly speaking only a
    generic term with some typing has been introduced; <verbatim|is an atom>
    means that we have introduced boolean valued terms, i.e., relations;

    <item>one can use <LaTeX>-commands like <verbatim|\\preccurlyeq> for
    symbols; using some <LaTeX>-tools these can be typeset like
    <math|\<preccurlyeq\>>;

    <item>the symbolic patterns like <verbatim|f : x \<less\>-\<gtr\> y> or
    <verbatim|x and y are equipollent> can be chosen rather freely, but there
    are some restrictions to allow the proper parsing of various constructs:
    we cannot write <verbatim|x and y have THE same cardinality> since the
    article <verbatim|the> signals that some unique value or so is taken; so
    we leave out the <verbatim|the>;

    <item>there is a tradeoff between definitions and abbreviations. Minor
    definitions are sometimes better treated as abbreviations by the
    <verbatim|Let <text-dots> stand for <text-dots>> construct. These
    abbreviations are already resolved by the parser and don't enter the
    first-order translation of texts.

    <item>The first order translations can be seen by letting Naproche-SAD
    run with the <verbatim|-T> option: <verbatim|stack exec Naproche-SAD --
    examples/regular_successor.ftl -T>
  </itemize-minus>

  Now we want to prove the first property:

  <\quote-env>
    <verbatim|Lemma 78a1. x ~ x.>
  </quote-env>

  This is canonically proved using the identity function on <math|x>. We
  provide that function also in the preliminaries:

  <\quotation>
    <verbatim|Signature. id x is a function such that id x : x
    \\leftrightarrow x.>
  </quotation>

  The automatic theorem prover (ATP) eprover is able to prove the Lemma using
  <verbatim|id x>.

  Here is a text which proves that <math|\<sim\>> is an equivalence relation,
  corresponding to the original scriptum.

  <\quote-env>
    <\verbatim>
      # Preliminaries

      \;

      Let x,y,z stand for sets.

      \;

      Let f,g stand for functions.

      \;

      Signature. f : x \\rightarrow y is an atom.

      Signature. f : x \\leftrightarrow y is an atom.

      Signature. f is injective is an atom.

      \;

      Signature. id x is a function such that id x : x \\leftrightarrow x.

      \;

      Signature. Assume f : x \\leftrightarrow y.\ 

      inv(f,x,y) is a function such that inv(f,x,y) : y \\leftrightarrow x.

      \;

      Signature.

      Assume f : x \\leftrightarrow y. Assume g : y \\leftrightarrow z.

      comp(g,f,x,y,z) is a function such that comp(g,f,x,y,z) : x
      \\leftrightarrow z.

      \;

      # 8 Cardinalities

      \;

      Definition 77a. x \\sim y iff exists f f : x \\leftrightarrow y.

      Let x and y are equipollent stand for x \\sim y.

      Let x and y are equipotent stand for x \\sim y.

      Let x and y have same cardinality stand for x \\sim y. # "the same" not
      accepted.

      Let x \\nsim y stand for not x \\sim y.

      Definition 77b. x \\preccurlyeq y iff\ 

      exists f (f : x \\rightarrow y and f is injective).

      # Definition 77c.

      Let x \\preccurly y stand for x \\preccurlyeq y and x \\nsim y.

      \;

      Lemma 78a1.

      x \\sim x.

      Lemma 78a2.

      If x \\sim y then y \\sim x.

      Lemma 78a3.

      If x \\sim y and y \\sim z then x \\sim z.
    </verbatim>
  </quote-env>

  Note:

  <\itemize-minus>
    <item>The proofs of the Lemmas are based on the existence of certain
    (abstract) functions through the signature extensions; eprover finds
    these proofs without further help;

    <item>the preliminaries are intended to describe aspects of a standard
    model of sets and functions; if one would leave out some preconditions of
    the signature extensions, the axioms get even stronger, but they may no
    longer correspond to standard models.
  </itemize-minus>

  Conclusions:

  <\itemize-minus>
    <item>The preliminaries contain abstract operations on functions like
    inversion and composition which one would find in a category of
    isomorphisms;

    <item>In a more comprehensive set theoretical approach, the preliminaries
    would be the result of a theory of functions;

    <item>Although ForTheL is part of natural language, the requirement for
    grammatical acceptance and logic correctness are much more strict and
    subtle than in ordinary (mathematical) language since there is no
    intelligent reader who is able to complete incomplete specifications.
  </itemize-minus>
</body>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|?>>
  </collection>
</references>