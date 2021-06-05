/*
 *  Specification of the ELL to CSR and COO to CSR
 *  translation algorithms
 *p[
 */

open structure
open behavior

-- translate COO to CSR
pred coocsr [d: COO, c: CSR] {
 maxnz = #d.A 
 for i in range[maxnz] do
     c.A[i] = d.val[i]
     c.JA[i] = d.col_ptr[i]
     c.IA[coo.row_ptr[i].add[1]] = c.IA[coo.row_ptr[i].add[1]].add[1]
 for i in range [d.rows] do
     c.IA[i.add[1]] = c.IA[i].add[c.IA[i.add[1]]];

}

-- translate ELL to CSR
pred ellcsr [e: ELL, c: CSR] {
  c.rows = e.rows
  c.cols = e.cols
  c.IA[0] = 0
  #c.IA = c.rows.add[1]
  some iter: Int->Int->Int, kpos: Int->Int {
    table[range[e.rows]->range[e.maxnz], iter]
    kpos[0] = 0
    #kpos = add[#iter, 1]
    #c.A = kpos.end
    #c.JA = kpos.end
    all i: range[e.rows] {
      all k: range[e.maxnz] |
        let t = iter[i][k], t' = t.add[1] |
          e.coef[i][k] != Zero => {
            c.A[kpos[t]] = e.coef[i][k]
            c.JA[kpos[t]] = e.jcoef[i][k]
            kpos[t'] = kpos[t].add[1]
          } else 
            kpos[t'] = kpos[t]
      c.IA[i.add[1]] = kpos[end[iter, i].add[1]]
    }
  }
}

-- establish iteration table by adding time column to end of relation r
pred table [r: Int->Int, iter: Int->Int->Int] {
  #iter = #r                -- same size as r
  iter.Int = r              -- make left side = r
  c3[iter] = range[#r]      -- make right side = time stamps
  all i, i': r.Int,
      j, j': Int.r,
      t, t': range[#r] {
    i->j->t in iter and i'->j'->t' in iter and t < t' =>
      i <= i' and (i = i' => j < j')
  }
}

-- third column of a ternary relation
fun c3 [r: Int->Int->Int]: Int {
  Int.(Int.r)
}

-- the last iteration of the inner loop for outer loop i'
fun end [iter: Int->Int->Int, i': Int]: Int {
  let times = {t: Int | some i, k: Int | i->k->t in iter and i <= i' } |
    some times => max[times] else 0
}

/*
 * Below we perform three checks:
 * 
 *   1. alphaValid checks that the abstraction functions map
 *      valid sparse representations to valid dense representations
 *
 *   2. preservesRep checks that the translation algorithm results
 *      in a valid CSR matrix
 *
 *   3. translateValid checks that the resulting CSR matrix
 *      represents the same dense matrix as the original ELL
 */  

assert alphaValid {
  all e: ELL, m: Matrix |
    I[e] and alpha[e, m] => I[e]
  all c: CSR, m: Matrix |
    I[c] and alpha[c, m] => I[m]
}

assert preservesRep {
  all e: ELL, c: CSR |
    I[e] and ellcsr[e, c] => I[c]
}

assert translateValid {
  all e: ELL, c: CSR, m: Matrix |
    I[e] and ellcsr[e, c] => (alpha[e, m] <=> alpha[c, m])
}

assert alphaValidCOOtoCSR {
  all d: COO, m: Matrix |
    I[d] and alpha[d, m] => I[d]
  all c: CSR, m: Matrix |
    I[c] and alpha[c, m] => I[m]
}

assert preservesRepCOOtoCSR {
  all d: COO, c: CSR |
    I[d] and coocsr[d, c] => I[c]
}

assert translateValidCOOtoCSR {
  all d: COO, c: CSR, m: Matrix |
    I[d] and coocsr[d, c] => (alpha[d, m] <=> alpha[c, m])
}

check alphaValid for 1 Matrix, 0 COO, 1 ELL, 1 CSR, 3 Value
check preservesRep for 0 Matrix, 0 COO, 1 ELL, 1 CSR, 3 Value
check translateValid for 1 Matrix, 0 COO, 1 ELL, 1 CSR, 3 Value
