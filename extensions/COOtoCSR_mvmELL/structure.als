module structure

/*
 * Specification of dense matrices and COO, ELL and CSR sparse
 * format representations
 *
 */

sig Value {}
one sig Zero extends Value {}

sig Matrix {
  rows, cols: Int,
  vals: Int->Int->lone Value
}

sig COO {
  rows, cols: Int,
  row_ptr, col_ptr: Int->lone Int,
  A: Int->lone Value
}

sig ELL {
  rows, cols, maxnz: Int,
  coef: Int->Int->lone Value,
  jcoef: Int->Int->lone Int
}

sig CSR {
  rows, cols: Int,
  A: Int->lone Value,
  IA, JA: Int->lone Int
}

-- arrays of the ELL format are 2D, arrays of COO, CSR format are 1D
fact {
  all e: ELL | Array2D[e.coef] and Array2D[e.jcoef]
  all c: CSR | Array1D[c.A] and Array1D[c.IA] and Array1D[c.JA]
  all d: COO | Array1D[d.A] and Array1D[d.row_ptr] and Array1D[d.col_ptr]
}

-- dense matrix abstract invariant
pred I [m: Matrix] {
  m.rows >= 0
  m.cols >= 0
  m.vals.univ = range[m.rows]->range[m.cols]
}

-- COO concrete invariant
pred I [d: COO] {
  d.rows >= 0
  d.cols >= 0
  d.row_ptr[0] = 0
  d.col_ptr[0] = 0
  #d.A = #d.row_ptr           -- A and row_ptr are same length
  #d.A = #d.col_ptr           -- A and col_ptr are same length
  Zero not in d.A[Int]   -- A cannot contain 0

  -- values of row_ptr are monotonically increasing
  all i: range[d.rows] |
    d.row_ptr[i] <= d.row_ptr[i.add[1]]

  -- values of col_ptr are monotonically increasing
  all i: range[d.cols] |
    d.col_ptr[i] <= d.col_ptr[i.add[1]]

  -- row indices are valid
  all j: d.row_ptr[Int] |
    j in range[d.rows]

  -- column indices are valid
  all j: d.col_ptr[Int] |
    j in range[d.cols]

  -- column indices appear once per row
  all i: range[d.rows] |
    let a = d.row_ptr[i], b = d.row_ptr[i.add[1]] |
      d.col_ptr.slice[a, b].valsUnique
}

-- ELL concrete invariant
pred I [e: ELL] {
  e.rows >= 0
  e.cols >= 0
  e.maxnz >= 0
  e.maxnz <= e.cols
  e.coef.univ = range[e.rows]->range[e.maxnz]   -- set i->j for coef
  e.jcoef.univ = range[e.rows]->range[e.maxnz]  -- set i->j for jcoef

  -- column indices are valid (include -1 placeholder)
  all j: e.jcoef[Int][Int] |
    j in range[-1, e.cols]

  -- column indices can appear once per row (-1 excepted)
  all i: range[e.rows] |
    all j: range[e.cols] |
      #e.jcoef[i].j <= 1

  -- enforce placeholders are at same locations within coef and jcoef
  all i: range[e.rows] |
    all k: range[e.maxnz] |
      e.coef[i][k] = Zero <=> e.jcoef[i][k] = -1
}

-- CSR concrete invariant
pred I [c: CSR] {
  c.rows >= 0
  c.cols >= 0
  c.IA[0] = 0
  c.IA.end = #c.A        -- last value of IA is length of A
  #c.IA = c.rows.add[1]  -- length of IA is rows + 1
  #c.A = #c.JA           -- A and JA are same length
  Zero not in c.A[Int]   -- A cannot contain 0

  -- values of IA are monotonically increasing
  all i: range[c.rows] |
    c.IA[i] <= c.IA[i.add[1]]

  -- column indices are valid
  all j: c.JA[Int] |
    j in range[c.cols]

  -- column indices appear once per row
  all i: range[c.rows] |
    let a = c.IA[i], b = c.IA[i.add[1]] |
      c.JA.slice[a, b].valsUnique
}

-- relation is a 1D array (indices range from 0 to n-1)
pred Array1D [a: Int->univ] {
  a.univ = range[#a]
}

-- relation is a 2D array (indices range from 0 to rows-1, 0 cols-1)
pred Array2D [a: Int->Int->univ] {
  a.univ.univ = range[#a.univ.univ]
  let s = #a[0] | all i: a.univ.univ | a[i].univ = range[s]
}

-- values in 1D array are unique
pred valsUnique [s: Int->univ] {
  #s = #s[Int]
}

-- last value in 1D array
fun end [s: Int->univ]: univ {
  s[max[s.univ]]
}

-- subset of 1D array in range [m, n-1]
fun slice [s: Int->univ, m, n: Int]: Int->univ {
  0 <= m and m < n and n <= #s => { i: Int, v: univ |
      (i.add[m])->v in s and i in range[n.sub[m]] } else {none->none}
}

-- the set [0, n-1]
fun range [n: Int]: set Int {
  { i: Int | 0 <= i and i < n }
}

-- the set [m, n-1]
fun range [m, n: Int]: set Int {
  { i: Int | m <= i and i < n }
}

-- generate a 5x5 dense matrix
pred showDense {
  some m: Matrix {
    m.rows = 5
    m.cols = 5
    I[m]
  }
}

run showDense for 1 Matrix, 0 COO, 0 ELL, 0 CSR, 5 Value

-- generate a 5x5 COO matrix
pred showCOO {
  some d: COO {
    d.rows = 5
    d.cols = 5
    I[d]
  }
}

run showCOO for 0 Matrix, 1 COO, 0 ELL, 0 CSR, 5 Value

-- generate a 5x5 ELL matrix
pred showELL {
  some e: ELL {
    e.rows = 5
    e.cols = 5
    I[e]
  }
}

run showELL for 0 Matrix, 0 COO,  1 ELL, 0 CSR, 5 Value

-- generate a 5x5 CSR matrix
pred showCSR {
  some c: CSR {
    c.rows = 5
    c.cols = 5
    I[c]
  }
}

run showCSR for 0 Matrix, 0 COO, 0 ELL, 1 CSR, 5 Value
