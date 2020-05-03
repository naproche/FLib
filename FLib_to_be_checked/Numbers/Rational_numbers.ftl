% rational numbers and integers

[number/-s] [devide/-s]
[ontored on]

\begin{signature} A rational number is a notion. \end{signature}
Let $q,r,s$ stand for rational numbers.

\begin{signature} $0$ is a rational number.\end{signature}
\begin{signature} $1$ is a rational number.\end{signature}
\begin{signature} $q + r$ is a rational number.\end{signature}
\begin{signature} $-q$ is a rational number.\end{signature}
\begin{signature} $q * r$ is a rational number.\end{signature}
\begin{signature} Assume $q \neq 0$. $\inv{q}$ is a rational number.
\end{signature}

% The rational numbers form a field:

\begin{axiom} $0 \neq 1$. \end{axiom}
\begin{axiom} $q + ( r + s) = (q + r) + s$.\end{axiom}
\begin{axiom} $q + r = r + q$.\end{axiom}
\begin{axiom} $q + 0 = q$.\end{axiom}
\begin{axiom} $q + -q = 0$.\end{axiom}
\begin{axiom} $q * ( r * s) = (q * r) * s$.\end{axiom}
\begin{axiom} $q * r = r * q$.\end{axiom}
\begin{axiom} $q * 1 = q$.\end{axiom}
\begin{axiom} If $q \neq 0$ then $q * \inv{q} = 1$.\end{axiom}
\begin{axiom} $q * (r + s) = (q * r) + (q * s)$.\end{axiom}

\begin{signature} A natural number is a rational number. 
\end{signature}

Let $n,m,k$ denote natural numbers.

\begin{axiom} $n * m$ is a natural number.\end{axiom}

\begin{definition} $n | m$ iff there exists $k$ such that $k * n = m$. \end{definition}
Let $n$ divides $m$ stand for $n | m$.
Let a divisor of $m$ stand for a natural number that divides $m$.

\begin{definition} $n$ and $m$ are coprime iff $n$ and $m$ have no common divisor.
\end{definition}

\begin{signature} $n$ is prime is an atom. \end{signature}

Let $p$ denote a prime natural number.

\begin{axiom} $p \neq 0$.\end{axiom}

\begin{axiom} $p | n * m \Rightarrow p | n \vee p | m$.\end{axiom}

\begin{axiom} There exist coprime $m,n$ such that $m * q = n$.
\end{axiom}

Let $q^2$ stand for $q * q$.

\begin{theorem} $p = q^2$ for no rational number $q$ \end{theorem}
\begin{proof}
Assume the contrary. Take a rational number $q$ such that $p = q^2$.
Take coprime $m,n$ such that $m * q = n$. Then $p * m^2 = n^2$.
Therefore $p$ divides $n$. Take a natural number $k$ such that 
$n = k * p$.
Then $p * m^2 = p * (k * n)$.
Therefore 
$$ m^2 = (\inv{p}*p)*m^2 = \inv{p}*(p*m^2) = \inv{p} * (p*(k*n)) =
(\inv{p}*p)*(k*n) = k * n = k*(k*p) = k^2 * p.$$
Hence $p$ divides $m$. Contradiction.
\end{proof}.



