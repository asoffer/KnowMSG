function factor(n) {
  let result = {};
  for (let i = BigInt(2); i * i < n; ++i) {
    if (n % i == 0) {
      n /= i;
      if (result[i] === undefined) {
        result[i] = BigInt(1);
      } else {
        ++result[i];
      }
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

class Factorization {
  constructor(number) {
    this._factorization = factor(number);
  }

  primeFactors() {
    return Object.entries(this._factorization).map(
      (key, value) => ({prime: BigInt(key), exponent: value}));
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

function getInput() {
  return BigInt(document.getElementById("input").value);
}

function constructGroupOrder(n) {
  return {
    order: n,
    factoredOrder: undefined,
    sylowSubgroupCountOptions: undefined
  };
}

function factored(groupOrder) {
  if (groupOrder.factoredOrder === undefined) {
    groupOrder.factoredOrder = new Factorization(groupOrder.order);
  }
  return groupOrder.factoredOrder;
}

function sylowSubgroupCountOptions(groupOrder) {
  function countSylowSubgroupOptions() {
    result = {};
    const factorization = factored(groupOrder);
    for (const {prime, exponent} of factorization.primeFactors()) {
      const sylowSubgroupSize = prime ** exponent;
      const sylowSubgroupIndexFactorization = factored(groupOrder);
      sylowSubgroupIndexFactorization.divideBy(Factorization(sylowSubgroupSize));
      result[p] = sylowSubgroupIndexFactorization.allFactors().filter(
        number => number % sylowSubgroupSize == 1);
    }
    return result;
  }

  if (groupOrder.sylowSubgroupCountOptions === undefined) {
    groupOrder.sylowSubgroupCountOptions = countSylowSubgroupOptions();
  }
  return groupOrder.SylowSubgroupCount;
}

function isOne(groupOrder) {
  if (groupOrder.order == 1) { return ""; }
  return null;
}

function isSporadicGroup(groupOrder) {
  const sporadicGroups = [
    { name: "a Mathieu group", symbol: "M_{11}", order: BigInt("7920"), },
    { name: "a Mathieu group", symbol: "M_{12}", order: BigInt("95040"), },
    { name: "a Mathieu group", symbol: "M_{22}", order: BigInt("443520"), },
    { name: "a Mathieu group", symbol: "M_{23}", order: BigInt("10200960"), },
    { name: "a Mathieu group", symbol: "M_{24}", order: BigInt("244823040"), },
    { name: "a Janko group", symbol: "J_1", order: BigInt("175560"), },
    { name: "a Janko group", symbol: "J_2", order: BigInt("604800"), },
    { name: "a Janko group", symbol: "J_3", order: BigInt("50232960"), },
    { name: "a Janko group", symbol: "J_4", order: BigInt("86775571046077562880"), },
    { name: "a Conway group", symbol: "Co_1", order: BigInt("4157776806543360000"), },
    { name: "a Conway group", symbol: "Co_2", order: BigInt("42305421312000"), },
    { name: "a Conway group", symbol: "Co_3", order: BigInt("495766656000"), },
    { name: "a Fischer Group", symbol: "Fi_{22}", order: BigInt("64561751654400"), },
    { name: "a Fischer Group", symbol: "Fi_{23}", order: BigInt("4089470473293004800"), },
    { name: "a Fischer Group", symbol: "Fi_{24'}", order: BigInt("1255205709190661721292800"), },
    { name: "the Higman-Sims group", symbol: "HS", order: BigInt("44352000"), },
    { name: "the McLaughlin group", symbol: "McL", order: BigInt("898128000"), },
    { name: "the Held group", symbol: "He", order: BigInt("4030387200"), },
    { name: "the Rudvalis group", symbol: "Ru", order: BigInt("145926144000"), },
    { name: "the Suzuki sporadic group", symbol: "Suz", order: BigInt("448345497600"), },
    { name: "the O'Nan group", symbol: "O'N", order: BigInt("460815505920"), },
    { name: "the Harada-Norton group", symbol: "HN", order: BigInt("273030912000000"), },
    { name: "the Lyons group", symbol: "Ly", order: BigInt("51765179004000000"), },
    { name: "the Thompson group", symbol: "Th", order: BigInt("90745943887872000"), },
    { name: "the Baby Monster group", symbol: "B", order: BigInt("4154781481226426191177580544000000"), },
    { name: "the Fischer-Griess Monster, or the monster group", symbol: "M", order: BigInt("808017424794512875886459904961710757005754368000000000"), },
  ];
  for (group of sporadicGroups) {
    if (group.order == groupOrder.order) {
      return "";
    }
  }
  return null;
}

function hasPrimeOrder(groupOrder) {
  const primeFactorCount = factored(groupOrder);
  if (primeFactorCount == 1) {
    return "";
  }
  return null;
}

function isSimpleByClassificationTheorem(groupOrder) {
  // TODO: Implement me.
  return null;
}

function orderIsTwoModuloFour(groupOrder) {
  if (groupOrder.order >= 5 && groupOrder.order % BigInt(4) == 2) {
    return "";
  }
  return null;
}

function sylow(groupOrder) {

  n.ptr = n.primes.head.next
        while(n.ptr != n.primes.head){
            if(n.ptr.data.np.size == 1)
                return true;
            n.ptr = n.ptr.next;
        }

    return false;
}

function showProof(n) {
  const groupOrder = constructGroupOrder(n);

  const techniques = [
    isOne,
    isSporadicGroup,
    hasPrimeOrder,
    isSimpleByClassificationTheorem,
    orderIsTwoModuloFour,
  ];

  for (technique of techniques) {
    const result = technique(groupOrder);
    if (result === null) { console.log("p4ass"); continue; }
    console.log(result);
  }
}
