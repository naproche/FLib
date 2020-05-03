<TeXmacs|1.0.7.14>

<style|generic>

<\body>
  <doc-data|<doc-title|There are infinitely many primes>|<doc-date|<date|>>>

  <new-theorem|signature|Signature> <new-theorem|axiom|Axiom>
  <new-theorem|signaturep|Signature> <new-theorem|axiomp|Axiom>
  <new-theorem|definitionp|Definition> <new-theorem|theoremp|Theorem>
  <new-theorem|lemmap|Lemma>

  <assign|power|<macro|<with|math-font|cal|P>>>

  <assign|preimg|<macro|1|2|<arg|1><rsup|-1>[<arg|2>]>>

  <assign|Seq|<macro|1|2|{<arg|1>,\<ldots\>,<arg|2>}>>

  <assign|Set|<macro|1|2|3|{<arg|1><rsub|<arg|2>>,\<ldots\>,<arg|1><rsub|<arg|3>>}>>

  <assign|Product|<macro|1|2|3|<big|prod><rsub|i=<arg|2>><rsup|<arg|3>><arg|1><rsub|i>>>

  <assign|subfunc|<macro|1|2|<arg|1><rsub|<arg|2>>>>

  <assign|CC|<macro|<with|math-font|Bbb*|C>>>

  <assign|RR|<macro|<with|math-font|Bbb*|R>>>

  <assign|QQ|<macro|<with|math-font|Bbb*|Q>>>

  <assign|ZZ|<macro|<with|math-font|Bbb*|Z>>>

  <assign|NN|<macro|<with|math-font|Bbb*|N>>>

  <assign|NNplus|<macro|<with|math-font|Bbb*|N><rsup|+>>>

  \ 

  <section|I. Foundations>

  <subsection|1. Sets>

  <\signature>
    SetSort. A <with|font-series|bold|set> is a notion. Let <math|A,X,Y,Z>
    denote sets.
  </signature>

  <\signature>
    ElmSort. An <with|font-series|bold|element> is a notion. Let <math|x,y,z>
    denote elements.
  </signature>

  <\signature>
    EOfElem. An <with|font-series|bold|element of> <math|X> is an element.
    Let <math|x> belongs to <math|X> stand for <math|x> is an element of
    <math|X>. Let <math|x> is in <math|X> stand for <math|x> belongs to
    <math|X>. Let <math|x\<in\>X> stand for <math|x> is in <math|X>.
  </signature>

  <\definition>
    DefEmp. <math|\<emptyset\>> is a set that has no elements. Let <math|X>
    is <with|font-series|bold|empty> stand for <math|X=\<emptyset\>>. Let
    <math|X> is <with|font-series|bold|nonempty> stand for
    <math|X\<neq\>\<emptyset\>>.
  </definition>

  <\definition>
    DefSub. A <with|font-series|bold|subset> of <math|Y> is a set <math|X>
    such that every element of <math|X> belongs to <math|Y>. Let
    <math|X\<subseteq\>Y> stand for <math|X> is a subset of <math|Y>.
  </definition>

  <\lemma>
    SubRefl. <math|X\<subseteq\>X>.
  </lemma>

  <\lemma>
    SubTrans. <math|X\<subseteq\>Y\<subseteq\>Z\<rightarrow\>X\<subseteq\>Z>.
  </lemma>

  <\axiom>
    SubASymm. <math|X\<subseteq\>Y\<subseteq\>X\<rightarrow\>X=Y>.
  </axiom>

  <subsection|2. Functions>

  <\signature>
    FunSort. A <with|font-series|bold|function> is a notion. Let <math|f,g,p>
    denote functions.
  </signature>

  <\signature>
    DomSet. <math|<text|dom>f> is a set. Let the
    <with|font-series|bold|domain> of <math|f> stand for <math|<text|dom>f>.
  </signature>

  <\signature>
    ImgElm. Let <math|x\<in\><text|dom>f>. <math|f<around|(|x|)>> is an
    element. Let <math|<subfunc|f|x>> stand for <math|f<around|(|x|)>>.
  </signature>

  <\definition>
    DefSImg. Let <math|X\<subseteq\><text|dom>f>.
    <math|f<around|[|X|]>=<around|{|f<around|(|x|)>\|x\<in\>X|}>>. Let
    <math|<text|ran>f> stand for <math|f<around|[|<text|dom>f|]>>. Let the
    <with|font-series|bold|range> of <math|f> stand for <math|<text|ran>f>.

    Let a function <with|font-series|bold|from> <math|X> stand for a function
    <math|f> such that <math|<text|dom>f=X>. Let a function
    <with|font-series|bold|from> <math|X> <with|font-series|bold|to> <math|Y>
    stand for a function <math|f> such that <math|<text|dom>f=X> and
    <math|<text|ran>f\<subseteq\>Y>.

    Let <math|f:X> stand for <math|f> is a function from <math|X>. Let
    <math|f:X-\<gtr\>Y> stand for <math|f> is a function from <math|X> to
    <math|Y>.
  </definition>

  <\lemma>
    ImgRng. Let <math|x\<in\><text|dom>f>. <math|f<around|(|x|)>> belongs to
    <math|<text|ran>f>.
  </lemma>

  <\definition>
    DefRst. Let <math|X\<subseteq\><text|dom>f>. <math|f\<upharpoonright\>X>
    is a function <math|g> from <math|X> such that for every <math|x\<in\>X>
    <math|g<around|(|x|)>=f<around|(|x|)>>.
  </definition>

  <subsection|3. Numbers>

  <\signature>
    NatSort. A <with|font-series|bold|number> is a notion. Let
    i,j,k,l,m,n,q,r denote numbers.
  </signature>

  <\definition>
    Nat. <math|<NN>> is the set of numbers.
  </definition>

  <\signature>
    SortsC. <math|0> is a number. Let <math|x> is
    <with|font-series|bold|nonzero> stand for <math|x\<neq\>0>.
  </signature>

  <\signature>
    SortsC. <math|1> is a nonzero number.
  </signature>

  <\signature>
    SortsB. <math|m+n> is a number.
  </signature>

  <\signature>
    SortsB. <math|m\<cdot\>n> is a number.
  </signature>

  <\axiom>
    AddAsso. <math|<around|(|m+n|)>+l=m+<around|(|n+l|)>>.
  </axiom>

  <\axiom>
    AddZero. <math|m+0=m=0+m>.
  </axiom>

  <\axiom>
    AddComm. <math|m+n=n+m>.
  </axiom>

  <\axiom>
    MulAsso. <math|<around|(|m\<cdot\>n|)>\<cdot\>l=m\<cdot\><around|(|n\<cdot\>l|)>>.
  </axiom>

  <\axiom>
    MulUnit. <math|m\<cdot\>1=m=1\<cdot\>m>.
  </axiom>

  <\axiom>
    MulZero. <math|m\<cdot\>0=0=0\<cdot\>m>.
  </axiom>

  <\axiom>
    MulComm. <math|m\<cdot\>n=n\<cdot\>m>.
  </axiom>

  <\axiom>
    AMDistr. <math|m\<cdot\><around|(|n+l|)>=<around|(|m\<cdot\>n|)>+<around|(|m\<cdot\>l|)>>
    and <math|<around|(|n+l|)>\<cdot\>m=<around|(|n\<cdot\>m|)>+<around|(|l\<cdot\>m|)>>.
  </axiom>

  <\axiom>
    AddCanc. If <math|l+m=l+n> or <math|m+l=n+l> then <math|m=n>.
  </axiom>

  <\axiom>
    MulCanc. Assume that <math|l> is nonzero. If <math|l\<cdot\>m=l\<cdot\>n>
    or <math|m\<cdot\>l=n\<cdot\>l> then <math|m=n>.
  </axiom>

  <\axiom>
    ZeroAdd. If <math|m+n=0> then <math|m=0> and <math|n=0>.
  </axiom>

  <\lemma>
    ZeroMul. If <math|m\<cdot\>n=0> then <math|m=0> or <math|n=0>.
  </lemma>

  <\definition>
    DefLE. <math|m\<leq\>n> iff there exists <math|l> such that <math|m+l=n>.
  </definition>

  <\definition>
    DefDiff. Assume that <math|m\<leq\>n>. <math|n-m> is a number <math|l>
    such that <math|m+l=n>.
  </definition>

  <\lemma>
    LERefl. <math|m\<leq\>m>.
  </lemma>

  <\lemma>
    LETran. <math|m\<leq\>n\<leq\>l\<rightarrow\>m\<leq\>l>.
  </lemma>

  <\lemma>
    LEAsym. <math|m\<leq\>n\<leq\>m\<rightarrow\>m=n>.
  </lemma>

  Let <math|m\<less\>n> stand for <math|m\<neq\>n> and <math|m\<leq\>n>.

  <\axiom>
    LETotal. <math|m\<leq\>n> or <math|n\<less\>m>.
  </axiom>

  <\lemma>
    MonAdd. Assume that <math|l\<less\>n>. Then <math|m+l\<less\>m+n> and
    <math|l+m\<less\>n+m>.
  </lemma>

  <\lemma>
    MonMul. Assume that <math|m> is nonzero and <math|l\<less\>n>. Then
    <math|m\<cdot\>l\<less\>m\<cdot\>n> and
    <math|l\<cdot\>m\<less\>n\<cdot\>m>.
  </lemma>

  <\axiom>
    LENTr. <math|n=0> or <math|n=1> or <math|1\<less\>n>.
  </axiom>

  <\lemma>
    MonMul2. <math|m\<neq\>0\<rightarrow\>n\<leq\>n\<cdot\>m>.
  </lemma>

  <\proof>
    Let <math|m\<neq\>0>. Then <math|1\<leq\>m>.
  </proof>

  <\signature>
    InbuiltForthelInductionRelation. <math|m\<precprec\>n> is an atom.
  </signature>

  <\axiom>
    EmbeddingLessIntoInductionRelation. <math|m\<less\>n\<rightarrow\>m\<precprec\>n>.
  </axiom>

  <subsection|4. Finite Sets and Sequences>

  <\definitionp>
    <math|<Seq|m|n>=<around|{|i\<in\><NN>\|m\<leq\>i\<leq\>n|}>>.
  </definitionp>

  <\definitionp>
    Let <math|f> be a function such that <math|<Seq|m|n>\<subseteq\><text|dom>f>.
    <math|<Set|f|m|n>=<around|{|f<around|(|i|)>\|i\<in\><NN>\<wedge\>m\<leq\>i\<leq\>n|}>>.
  </definitionp>

  <\definitionp>
    <math|f> <with|font-series|bold|lists> <math|X> in <math|n> steps iff
    <math|<text|dom>f=<Seq|1|n>> and <math|X=<Set|f|1|n>>.
  </definitionp>

  <\definitionp>
    <math|X> is <with|font-series|bold|finite> iff there is a function
    <math|f> and a number <math|n> such that <math|f> lists <math|X> in
    <math|n> steps.
  </definitionp>

  <\definitionp>
    <math|X> is <with|font-series|bold|infinite> iff <math|X> is not finite.
  </definitionp>

  <section|II. Prime Numbers>

  <subsection|1. Divisibility>

  <\definition>
    DefDiv. <math|m> <with|font-series|bold|divides> <math|n> iff for some
    <math|l> <math|n=m\<cdot\>l>. Let <math|m\|n> denote <math|m> divides
    <math|n>. Let a <with|font-series|bold|divisor> of <math|n> denote a
    number that divides <math|n>.
  </definition>

  <\definition>
    DefQuot. Assume that <math|m> is nonzero and <math|m\|n>.
    <math|<frac|n|m>> is a number <math|l> such that <math|n=m\<cdot\>l>.
  </definition>

  <\lemma>
    DivTrans. <math|l<around|\||m|\|>*n\<rightarrow\>l\|n>.
  </lemma>

  <\lemma>
    DivSum. Let <math|l\|m> and <math|l\|n>. Then <math|l\|m+n>. Indeed if
    <math|l> is nonzero then <math|m+n=l\<cdot\><around|(|<frac|m|l>+<frac|n|l>|)>>.
  </lemma>

  <\lemma>
    DivMin. Let <math|l\|m> and <math|l\|m+n>. Then <math|l\|n>.
  </lemma>

  <\proof>
    Assume that <math|l,n> are nonzero. Take <math|i> such that
    <math|m=l\<cdot\>i>. Take <math|j> such that <math|m+n=l\<cdot\>j>.

    Let us show that <math|i\<leq\>j>. Assume the contrary. Then
    <math|j\<less\>i>. <math|m+n=l\<cdot\>j\<less\>l\<cdot\>i=m>.
    <math|m\<leq\>m+n>. <math|m=m+n>. <math|n=0>. Contradiction. end.

    Take <math|k=j-i>. We have <math|<around|(|l\<cdot\>i|)>+<around|(|l\<cdot\>k|)>=<around|(|l\<cdot\>i|)>+n>.
    Hence <math|n=l\<cdot\>k>.
  </proof>

  <\lemma>
    DivLE. Let <math|m\|n\<neq\>0>. Then <math|m\<leq\>n>.
  </lemma>

  <\lemma>
    DivAsso. Let <math|l> be nonzero and divide <math|m>. Then
    <math|n\<cdot\><frac|m|l>=<frac|n\<cdot\>m|l>>.
  </lemma>

  <\proof>
    <math|<around|(|l\<cdot\>n|)>\<cdot\><frac|m|l>=l\<cdot\><frac|n\<cdot\>m|l>>.
  </proof>

  <\definitionp>
    <math|<NNplus>=<around|{|n\<in\><NN>\|n\<neq\>0|}>>.
  </definitionp>

  <\signaturep>
    Let <math|f:<Seq|m|n>-\<gtr\><NNplus>>. <math|<Product|f|m|n>> is an
    element of <math|<NNplus>>.
  </signaturep>

  <\axiom>
    MultProd. Let <math|f:<Seq|m|n>-\<gtr\><NNplus>>. Let
    <math|m\<leq\>j\<leq\>n>. <math|<subfunc|f|j>> divides
    <math|<Product|f|m|n>>.
  </axiom>

  <subsection|2. Primes>

  Let <math|m> is <with|font-series|bold|trivial> stand for <math|m=0> or
  <math|m=1>. Let <math|m> is <with|font-series|bold|nontrivial> stand for
  <math|m\<neq\>0> and <math|m\<neq\>1>.

  <\definition>
    DefPrime. <math|q> is <with|font-series|bold|prime> iff <math|q> is
    nontrivial and for every divisor <math|m> of <math|q> <math|m=1> or
    <math|m=q>.
  </definition>

  Let <math|m> is <with|font-series|bold|compound> stand for <math|m> is not
  prime.

  <\lemma>
    PrimDiv. Every nontrivial <math|k> has a prime divisor.
  </lemma>

  <with|font-series|bold|Proof> by induction on <math|k>. Let <math|k> be
  nontrivial. Case <math|k> is prime. Obvious. Case <math|k> is compound.
  Take a divisor <math|m> of <math|k> such that <math|m\<neq\>1> and
  <math|m\<neq\>k>. #<math|m\<neq\>0>. <math|m> is nontrivial and
  <math|m\<precprec\>k>. Take a prime divisor <math|n> of <math|m>. <math|n>
  is a prime divisor of <math|k>. end. qed.

  <\theoremp>
    The set of prime numbers is infinite.
  </theoremp>

  <\proof>
    Let <math|A> be a finite set of prime numbers. Take a function <math|p>
    and a number <math|r> such that <math|p> lists <math|A> in <math|r>
    steps. <math|<text|ran>p\<subseteq\><NNplus>>.
    <math|<Product|p|1|r>\<neq\>0>. Take <math|n=<Product|p|1|r>+1>. <math|n>
    is nontrivial. Take a prime divisor <math|q> of <math|n>.

    Let us show that <math|q> is not an element of <math|A>. Assume the
    contrary. Take <math|i> such that (<math|1\<leq\>i\<leq\>r> and
    <math|q=<subfunc|p|i>>). <math|<subfunc|p|i>> divides
    <math|<Product|p|1|r>> (by MultProd). Then <math|q> divides <math|1> (by
    DivMin). Contradiction. qed.

    Hence <math|A> is not the set of prime numbers.
  </proof>
</body>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|?>>
    <associate|auto-2|<tuple|1.1|?>>
    <associate|auto-3|<tuple|1.2|?>>
    <associate|auto-4|<tuple|1.3|?>>
    <associate|auto-5|<tuple|1.4|?>>
    <associate|auto-6|<tuple|2|?>>
    <associate|auto-7|<tuple|2.1|?>>
    <associate|auto-8|<tuple|2.2|?>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|I.
      Foundations> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|1. Sets
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2>>

      <with|par-left|<quote|1.5fn>|2. Functions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3>>

      <with|par-left|<quote|1.5fn>|3. Numbers
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4>>

      <with|par-left|<quote|1.5fn>|4. Finite Sets and Sequences
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|II.
      Prime Numbers> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-6><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|1. Divisibility
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-7>>

      <with|par-left|<quote|1.5fn>|2. Primes
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-8>>
    </associate>
  </collection>
</auxiliary>