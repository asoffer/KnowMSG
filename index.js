import {Factorization} from "./factorization.js"

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

function renderMath(element) {
  if (element.children.length == 0) {
    element.innerHTML = 
      element
      .textContent
      .split("$")
      .map((text, index) => {
        if (index % 2 == 0) {
          return text;
        } else {
          return katex.renderToString(text, {
            throwOnError: false
          });
        }
      })
      .join("");
  } else {
    for (const e of element.children) {
      renderMath(e);
    }
  }
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
  if (groupOrder.order == 1) {
    return `
    <p>
    The trivial group is the only group on one element, and has no proper 
    subgroup, let alone non-trivial normal ones, so it is vacuously simple.
    </p>
    `; 
  }

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
  for (const group of sporadicGroups) {
    if (group.order == groupOrder.order) {
      return `
      <p>
      The group $${group.symbol}$, ${group.name}, is a simple group of order $${group.order}$.
      </p>
      `;
    }
  }
  return null;
}

function burnsidesTheorem(groupOrder) {
  const primeFactors = factored(groupOrder).primeFactors();
  if (primeFactors.length == 2) {
    return `
    <p>
    Burnside's Theorem states that for primes $p$ and $q$, and positive integers
    $a$ and $b$, all groups of order $p^aq^b$ are solvable. Because
    $${groupOrder.order}$ is the product of two prime powers an group of this 
    order must be solvable, and therefore not simple.
    </p>

    <p>
    Know a more elementary proof? <a href="https://github.com/asoffer/KnowMSG/issues">File an issue!</a>
    </p>
    `;
  }
  return null;
}

function feitThompsonTheorem(groupOrder) {
  if (groupOrder.order % BigInt(2) == 1) {
    return `
    <p>
    The Feit-Thompson Theorem says that all groups of odd order are solvable. 
    A solvable simple group must be of prime order. Because
    $${groupOrder.order}$ is not prime, no group of order $${groupOrder.order}$
    is simple.
    </p>

    <p>
    Know a more elementary proof? <a href="https://github.com/asoffer/KnowMSG/issues">File an issue!</a>
    </p>
    `;
  }
  return null;
}

function isPrime(groupOrder) {
  const primeFactors = factored(groupOrder).primeFactors();
  if (primeFactors.length == 1 && primeFactors[0].exponent == 1) {
    let proof = `
    <p>
    Let $G$ be a group of order $${groupOrder.order}$. Lagrange's theorem tells
    us that the order of every subgroup group of $G$ divides
    $${groupOrder.order}$. Because $${groupOrder.order}$ is prime, the 
    only subgroups are the trivial group and $G$ itself, so these are the only 
    normal subgroups as well. Hence, $G$ is simple.
    </p>

    <p>
    Moreover, up to isomorphism, the only group of order $${groupOrder.order}$ 
    is the cyclic group $\\mathbb{Z}/${groupOrder.order}\\mathbb{Z}$.
    </p>
    `;
    if (groupOrder.order == 2) {
      proof += `
        <iframe width="420" height="315" 
         src="http://www.youtube.com/embed/UTby_e4-Rhg?autoplay=1" 
         frameborder="0" allowfullscreen></iframe>
      `;
    }
    return proof;
  }
  return null;
}

function isPrimePower(groupOrder) {
  const primeFactors = factored(groupOrder).primeFactors();
  if (primeFactors.length == 1) {
    const prime = primeFactors[0].prime;
    return `
    <p>
    Let $G$ be a group of order $${groupOrder.order}$. By the class equation,
    </p>
    <center>
      $\\left|G\\right|=\\left|Z(G)\\right|+\\sum_{g\\in O^*}[G:C_G(g)].$
    </center>

    <p>
    We know that $\\left|G\\right|$ is divisible by the prime $${prime}$.
    Moreover each term in the summation is an index of a subgroup of $G$
    which must therefore be divisible by $${prime}$ making the entire
    summation divisible by $${prime}$. It follows that $\\left|Z(G)\\right|$
    must also be divisible by $${prime}$. Thus either $Z(G)=G$, meaning $G$ is 
    abelian and therefore not simple, or $Z(G)$ is a proper normal subgroup of
    $G$, again implying that $G$ must not be simple.
    </p>
    `;
  }
  return null;
}

function isSimpleByClassificationTheorem(groupOrder) {
  // TODO: Implement me.
  return null;
}

function orderIsTwoModuloFour(groupOrder) {
  if (groupOrder.order >= 5 && groupOrder.order % BigInt(4) == 2) {
    return `
    <p>
    Let $G$ be a group of order $${groupOrder.order}$. By Cauchy's theorem, 
    $G$ has an element $g$ of order $2$. Because $G$ acts on itself by (left) 
    multiplication, there exists an injective homomorphism,
    $\\varphi: G \\to S_{\\left|G\\right|}$.
    </p>

    <p>
    Consider the cycle structure of $\\varphi(g)$. Because $g$ has order $2$,
    $\\varphi(g)$ must be the product of $2$-cycles. Moreover, $\\varphi(g)$
    cannot have any fixed points: A fixed point would correspond to an element
    $x\\in G$ for which $gx=g$, but $g$ is not the identity element. This means
    that $\\varphi(g)$ is the product of exactly $${groupOrder.order/BigInt(2)}$
    two-cycles.
    </p>

    <p>
    A two-cycle is an odd permutation, and the product of an odd number of odd 
    permutations is also an odd permutation. Thus,
    $\\varphi(g)\\not\\in A_{\\left|G\\right|}$.
    Because $A_{\\left|G\\right|}\\unlhd S_{\\left|G\\right|}$, we know that 
    $\\varphi(G)\\cap A_{\\left|G\\right|}\\unlhd \\varphi(G)$ and has index at 
    most two. Moreover, $\\varphi(g)$ is an element of $\\varphi(G)$ which is 
    not in the intersection, so we have produced a normal proper subgroup of 
    index two. Because $\\varphi(G)$ is isomorphic to $G$, there is a corresponding
    normal subgroup of $G$ and therefore $G$ is not simple.
    </p>
    `;
  }
  return null;
}

export function showProof(n) {
  const groupOrder = constructGroupOrder(n);

  const techniques = [
    isOne,
    isSporadicGroup,
    isPrime,
    isPrimePower,
    isSimpleByClassificationTheorem,
    orderIsTwoModuloFour,
    burnsidesTheorem,
    feitThompsonTheorem,
  ];

  for (const technique of techniques) {
    const result = technique(groupOrder);
    if (result === null) {
      continue;
    } else {
      const proofElement = document.getElementById("proof");
      proofElement.innerHTML = result;
      renderMath(proofElement);
      return;
    }
  }
}

(function() {
  const proveButton = document.getElementById("prove");
  proveButton.onclick = () => {
    const value = document.getElementById("input").value;
    showProof(BigInt(value));
  };
})();
