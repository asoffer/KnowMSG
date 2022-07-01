function factor(n) {
  let result = {};
  for (let i = BigInt(2); i * i <= n;) {
    if (n % i == 0) {
      n /= i;
      if (result[i] === undefined) {
        result[i] = BigInt(1);
      } else {
        ++result[i];
      }
    } else {
      ++i;
    }
  }

  if (n != 1) {
    if (result[n] === undefined) {
      result[n] = BigInt(1);
    } else {
      ++result[n];
    }
  }
  return result;
}

export class Factorization {
  constructor(number) {
    this._factorization = factor(number);
  }

  primeFactors() {
    return Object.entries(this._factorization).map(
      entry => ({prime: BigInt(entry[0]), exponent: entry[1]}));
  }

  divideBy(f) {
    for (const prime of Object.keys(f)) {
      this._factorization[prime] -= f[prime];
      if (this._factorization[prime] == 0) {
        delete this._factorization[prime];
      }
    }
  }

  allFactors() {
    let result = [1];
    for ({prime: p, exponent: e} of this.primeFactors()) {
      const newResults = results;
      for (let i = BigInt(0); i < e; ++i) {
        newResults = newResults.concat(result.map(x => x * (p ** e)));
      }
      results = newResults;
    }
    return result;
  }
};
