function Option(p,np){
    //pointers back
    this.p = p;
    this.n = p.n;

    this.np = np;

    this.proofComplete = false;
    this.proof = "";
}

Option.prototype = {
    toString: function(){
	return this.np.toString();
    },

    countTest: function(){
	if(this.proofComplete)
	    return false;

	    
	var ptr = this.n.primes.head.next;
	var count = 0;

	while(ptr != this.n.primes.head){

	    //for this prime, count with this np
	    if(ptr.data == this.p){
		if(this.p.pow > 1)
		    count += Math.pow(this.p.p, this.p.pow);
		else
		    count += this.np * (this.p.p - 1);
	    }
	    else{
		if(ptr.data.pow > 1)
		    count += Math.pow(ptr.data.p, ptr.data.pow);
		else
		    count += ptr.data.smallestNP().np * (ptr.data.p - 1);
	    }

	    ptr = ptr.next;
	}

	//FINISH ME, WHEN DO I NEED WHAT FOR COUNTING?
	this.proof = "<p>If $p$ divides $\\left|G\\right|$, but $p^2$ does not, then the Sylow $p$-subgroups of $G$ are all isomorphic to $" + zmod("p") + "$, and therefore are required to have trivial intersection. That is, if $p^2\\nmid\\left|G\\right|$, we can conclude that $G$ contains $n_p\\cdot(p-1)$ elements of order $p$. We conclude that $G$ has a minimum of";

	var ptr = this.n.primes.head.next;
	while(ptr != this.n.primes.head){
	    var p = (ptr.data == this.p ? this.p : ptr.data);
	    var np = (ptr.data == this.p ? this.np : ptr.data.smallestNP().np);

	    if(ptr.data.pow == 1){
		this.proof += "$$" + np + "\\cdot(" + p + " - 1)=" + np * (p.p - 1) + "\\mbox{ elements of order }" + p + "$$\n";
	    }
	    else{
		this.proof += "$$" + p.toStringWithPower() + "= " + Math.pow(p.p, p.pow) + "\\mbox{ non-identity elements in " + sylow(p) + "s }$$\n";
	    }

	    ptr = ptr.next;
	    
	}

	if(count >= this.n.n){
	    this.proof += "<p>This constitutes $" + count + "$ elements in Sylow subgroups in a group of order $" + this.n + "$";

	    this.proofComplete = true;
	}

	if(count == this.n.n){
	    this.proof += ", which leaves no room for an identity element";
	}
	this.proof += ".</p>";

	if(count >= this.n.n)
	    return true;
    },

    elementSizeTest: function(){
	if(this.proofComplete)
	    return false;

	//look at the normalizer of a sylow p group. given it's size, we know that it has an element of some order maximal. maybe this is too big?
	var normSize = new Num(this.n.n/this.np);
	var maxCyclic = normSize.maxOrder();

	if((new Num(maxCyclic)).sumOfPrimeDivisors() > this.np - 1){


	    this.proofComplete = true;
	    this.proof = "<p>Let  $P_{" + this.p + "}$ be a " + sylow(this.p) + ". Then $N_G(P_{" + this.p + "})$ is a group of order $" + (this.n.n/this.np) + "$. Any group of order $" + (this.n.n/this.np) + "$ has a cyclic subgroup of order $" + maxCyclic + "$. However, the normalizer $N_G(P_{" + this.p + "})$ is the stabilizer $P_{" + this.p + "}$ under the action of conjugation on the " + sylow(this.p) + "s of $G$, so instead of only embedding inside $S_{" + this.np + "}$, we actually know that it embeds inside $S_{" + (this.np - 1) + "}$. But $S_{" + (this.np - 1) + "}$ has no cyclic subgroups of order $" + maxCyclic + "$.</p>";


	    if(this.n.n == 3465){
		    console.log("&&" + this.np);
	    }

	    return true;
	}
	return false;
    },

    symmetricDivisorTest: function(){
	if(this.proofComplete)
	    return false;


	var ptr = this.n.primes.head.next;
	while(ptr != this.n.primes.head){
	    if(ptr.data.p <= this.np && (ptr.data.p << 1) > this.np){
		var norm = this.n.n/this.np;
		var other = factorial(this.np - ptr.data.p) * ptr.data.p * (ptr.data.p - 1);

		this.proof = "<p>We know that $G$ acts on the " + sylow(this.p) + "s by conjugation, and this action gives rise to a nontrivial map $\\phi: G\\to S_{n_{" + this.p + "}}=S_{" + this.np + "}$. If $G$ is to be simple, $\\phi$ must be injective, so we can think of $G$ as being a subgroup of $S_{" + this.np + "}$. Let $P_{" + ptr.data.p + "}$ be a " + sylow(ptr.data.p) + " of $G$. Since $" + ptr.data.p + "^2\\nmid\\left|S_{" + this.np + "}\\right|$, $P_{" + ptr.data.p + "}$ is also a " + sylow(ptr.data.p) + " of $S_{" + this.np + "}$. This means that $N_G(P_{" + ptr.data.p + "})\\le N_{S_{" + this.np + "}}(P_{" + ptr.data.p + "})$.";

		if(other % norm != 0){
		    this.proof += "We will show that for divisibility reasons, this cannot be.</p><p>We can explicitly count the number of elements in $S_{" + this.np + "}$ of order $" + ptr.data.p + "$. They come precisely from $" + ptr.data.p + "$-cycles, of which there are $$\\binom{" + this.np + "}{" + ptr.data.p + "}\\cdot (" + ptr.data.p + "-1)!$$ Since each such element is in precisely one " + sylow(ptr.data.p) + " of $S_{" + ptr.data.p + "}$, and each " + sylow(ptr.data.p) + " has exactly $" + (ptr.data.p - 1) + "$ elements of order $" + ptr.data.p + "$, there are $\\binom{" + this.np + "}{" + ptr.data.p + "}\\cdot (" + ptr.data.p + "-2)!$ " + sylow(ptr.data.p) + "s.</p><p>From the Sylow theorems, we know that $\\left|N_{S_{" + ptr.data.p + "}}(P_{" + ptr.data.p + "})\\right|=" + other + "$. We also know that $\\left|N_G(P_{" + ptr.data.p + "})\\right|=" + norm + "$. However, $N_G(P_{" + ptr.data.p + "})\\le N_{S_{" + ptr.data.p + "}}(P_{" + ptr.data.p + "})$, which contradicts Lagrange's theorem.</p>"
		    this.proofComplete = true;
		    return true;

		}

		else if(other == norm){
		    this.proof += "We will show that for divisibility reasons, this cannot be.</p><p>We can explicitly count the number of elements in $S_{" + this.np + "}$ of order $" + ptr.data.p + "$. They come precisely from $" + ptr.data.p + "$-cycles, of which there are $$\\binom{" + this.np + "}{" + ptr.data.p + "}\\cdot (" + ptr.data.p + "-1)!$$ Since each such element is in precisely one " + sylow(ptr.data.p) + " of $S_{" + ptr.data.p + "}$, and each " + sylow(ptr.data.p) + " has exactly $" + (ptr.data.p - 1) + "$ elements of order $" + ptr.data.p + "$, there are $\\binom{" + this.np + "}{" + ptr.data.p + "}\\cdot (" + ptr.data.p + "-2)!$ " + sylow(ptr.data.p) + "s.</p><p>From the Sylow theorems, we know that $\\left|N_{S_{" + this.np + "}}(P_{" + ptr.data.p + "})\\right|=" + other + "$. Moreover, we know that $G$ embeds into $A_{" + this.np + "}$, lest $G\\cap A_{" + this.np + "}\\lhd G$. So $N_{A_{" + this.np + "}}(P_{" + ptr.data.p + "}) = " + (other/2) + "$. We also know that $\\left|N_G(P_{" + ptr.data.p + "})\\right|=" + norm + "$. However, $N_G(P_{" + ptr.data.p + "})\\le N_{A_{" + this.np + "}}(P_{" + ptr.data.p + "})$, which contradicts Lagrange's theorem.</p>"
		    this.proofComplete = true;
		    return true;
		}
	    }

	    ptr = ptr.next;
	}

    },

    doubleNormalizerTest: function(){
	if(this.proofComplete)
	    return false;

	var ptr = this.n.primes.head.next;
	while(ptr != this.n.primes.head){
	    
	    //take a prime which divides n but not np
	    if(this.np % ptr.data.p != 0 && ptr.data.p != this.p.p){

		var norm = new Num(this.n.n/this.np);
		norm.computeFactorList();

		if(norm.kModM(1, ptr.data.p).size == 1 &&
		   ptr.data.p != this.p &&
		   ptr.data.incompleteNPSize() == 1 &&
		   (this.n.n/ptr.data.smallestNP()) % Math.pow(this.p.p, this.p.pow) != 0){


		    var exp = "";
		    if(ptr.data.pow > 1)
			exp = "^{" + ptr.data.pow + "}";

		    this.proof = "<p>Let $P_{" + this.p + "}$ be a " + sylow(this.p) + ". Then $N_G(P_{" + this.p + "})$ is a group of order $" + (this.n.n/this.np) + "$, and therefore has a " + sylow(ptr.data.p) + ", $P_{" + ptr.data.p + "}$. It is clear that $P_{" + ptr.data.p + "}$ is also a " + sylow(ptr.data.p) + " of $G$. Applying the Sylow counting technique to the group $N_G(P_{" + this.p + "})$, tells us that it contains exactly one " + sylow(ptr.data.p) + ", so $P_{" + ptr.data.p + "}\\lhd N_G(P_{" + this.p + "})$. Since every element of $P_{" + this.p + "}$ conjugates $P_{" + ptr.data.p + "}$ to itself, $P_{" + this.p + "}\\le N_G(P_{" + ptr.data.p + "})$. This means that $" + this.p + exp + "$ must divide the order of $N_G(P_{" + ptr.data.p + "})$. But we already know that $\\left|N_G(P_{" + ptr.data.p + "})\\right|=" + this.n + "/n_{" + ptr.data.p + "} = " + (this.n.n/ptr.data.smallestNP()) + "$, a contradiction.</p>";

		    this.proofComplete = true;
		    return true;
		}
	    }
	    ptr = ptr.next;
	}
    },

    largeIntersectionAbelianTest: function(){
	if(this.proofComplete)
	    return false;

	
	if(this.p.pow != 2 || this.n.countElements() + (Math.pow(this.p.p, 2) - 2) * this.np < this.n.n)
	    return true ;

	//we're looking for  divisors of p^a that ar larger than p^(a+1)
	var f = this.n.kModM(0, Math.pow(this.p.p, 2));
	var ptr = f.head.prev;

	while(Math.pow(this.p.p, 3) < ptr.data)
	    ptr = ptr.prev;

	ptr = ptr.next;

	if(this.n.n/ptr.data < this.n.divInject){
	    this.proof = "<p>Since the " + sylow("p") + " cannot intersect nontrivially for any prime $p$ such that $2\\nmid\\left|G\\right|$, at a minimum, we have ";
	    var counter = 0;

	    var ptr2 = this.n.primes.head.next;
	    while(ptr2 != this.n.primes.head){
		if(ptr2.data.p != this.p.p && ptr2.data.pow == 1){
		    this.proof += "$$" + ptr2.data.smallestNP() + "\\cdot(" + ptr2.data.toStringWithPower() + " - 1)=" + ptr2.data.smallestNP().np * (Math.pow(ptr2.data.p, ptr2.data.pow) - 1) + "\\mbox{ elements of order }" + ptr2.data.p + "$$\n";

		    counter += ptr2.data.smallestNP().np * (Math.pow(ptr2.data.p, ptr2.data.pow) - 1);
		}
		ptr2 = ptr2.next;
	    }

	    this.proof += "</p><p>Furthermore, for the primes $p$ such that $p^2$ divides $\\left|G\\right|$, there are at least two Sylow $p$-subgroups $P$ and $Q$. While they may have nontrivial intersection, if we are looking for a lower bound on the number of elements in Sylow $p$ subgroups of $G$, we must get $p^m$ elements from $P$ (where $p^m$ divides $\\left|G\\right|$, but $p^{m+1}$ does not), and at least one more element from $Q$. Thus, we get at very least";

	    ptr2 = this.n.primes.head.next;
	    while(ptr2 != this.n.primes.head){
		if(ptr2.data.p != this.p.p && ptr2.data.pow > 1){
		    this.proof += "$$" + ptr2.data.smallestNP() + "\\cdot(" + ptr2.data + " - 1)=" + ptr2.data.smallestNP().np * (ptr2.data.p - 1) + "\\mbox{ elements of order }" + ptr2.data.p + "^k$$\n";
		    counter += ptr2.data.smallestNP().np * (ptr2.data.p - 1);
		}
		ptr2 = ptr2.next;
	    }


	    this.proof += "for a total of $" + counter + "$ elements.</p><p>Then the " + sylow(this.p) + " subgroups cannot have trivial intersection, lest there be another $" + this.np + "\\cdot(" + this.p + "^{" + this.p.pow + "} - 1)$ elements. So there must be two distinct " + sylow(this.p) + "s of $G$, $P$ and $Q$, such that $[P:P\\cap Q]&lt; p^2$. As this index must be a power of $" + this.p + "$, and $P\\ne Q$, the index must be $" + this.p + "$. That is, $\\left|P\\cap Q\\right|=" + this.p + "$.</p><p>Since every group of order $" + this.p.toStringWithPower() + "$ is abelian, $P\\cap Q\\lhd P$, so $P\\le N_G(P\\cap Q)$. Similarly, $Q\\le N_G(P\\cap Q)$, so $PQ\\subseteq N_G(P\\cap Q)$. We can therefore bound the size of the normalizer by $$\\left|N_G(P\\cap Q)\\right|\\ge\\left|PQ\\right|=\\frac{\\left|P\\right|\\cdot\\left|Q\\right|}{\\left|P\\cap Q\\right|}=" + this.p + "^{" + (this.p.pow + 1) + "}.$$ We also know that $P\\le N_G(P\\cap Q)$, so $\\left|N_G(P\\cap Q)\\right|$ is a divisor of $\\left|G\\right|$ which has $\\left|P\\right|=" + this.p.p + "^{" + this.p.pow + "}$ as a proper divisor. Then it is easily verified that $\\left|N_G(P\\cap Q)\\right|$ is at least $" + ptr.data + "$. But then $N_G(P\\cap Q)$ is a subgroup of $G$ of index no more than $" + (this.n.n/ptr.data) + "$. Since $G$ acts transitively on the left cosets of $N_G(P\\cap Q)$ by left multiplication, we have a nontrivial map $\\phi: G\\to S_{" + (this.n.n/ptr.data) + "}$. Contradiction.</p>";
	    this.proofComplete = true;
	    return true;
	}
    },

    largeIntersectionTest: function(){
	if(this.proofComplete)
	    return false;

	
	if(this.p.pow == 1 || this.np % Math.pow(this.p.p, 2) == 1)
	    return false;

	//we're looking for  divisors of p^a that ar larger than p^(a+1)
	var f = this.n.kModM(0, Math.pow(this.p.p, this.p.pow));
	var ptr = f.head.prev;

	while(ptr.data > Math.pow(this.p.p, this.p.pow + 1))
	    ptr = ptr.prev;

	ptr = ptr.next;
	var exp = "";
	if(this.p.pow > 2)
	    exp = "^{" + (this.p.pow + 1) + "}";

	//now we know there are two sylow subgroups with large intersection.
	//both p and q are in the normalize of their intersection
	console.log(this.n.n + "   " + ptr.data + "    " + this.n.divInject);
	if(this.n.n/ ptr.data < this.n.divInject){
	    this.proof = "<p>Since $n_{" + this.p + "}\\not\\equiv 1(\\bmod" + this.p + "^2)$, there must be two distinct " + sylow(this.p) + "s of $G$, $P$ and $Q$, such that $[P:P\\cap Q]&lt; p^2$. As this index must be a power of $" + this.p + "$, and $P\\ne Q$, the index must be $" + this.p + "$. That is, $\\left|P\\cap Q\\right|=" + this.p + exp + "$.</p><p>However, $P\\cap Q$ is a $" + this.p + "$-subgroup of $P$ with index divisible by $" + this.p + "$, so $" + this.p + "$ divides $[N_P(P\\cap Q):P\\cap Q]$, meaning $N_P(P\\cap Q)=P$. This means, $P\\cap Q\\lhd P$, so $P\\le N_G(P\\cap Q)$. Similarly, $Q\\le N_G(P\\cap Q)$, so $PQ\\subseteq N_G(P\\cap Q)$. We can therefore bound the size of the normalizer by $$\\left|N_G(P\\cap Q)\\right|\\ge\\left|PQ\\right|=\\frac{\\left|P\\right|\\cdot\\left|Q\\right|}{\\left|P\\cap Q\\right|}=" + this.p + "^{" + (this.p.pow + 1) + "}.$$ We also know that $P\\le N_G(P\\cap Q)$, so $\\left|N_G(P\\cap Q)\\right|$ is a divisor of $\\left|G\\right|$ which has $\\left|P\\right|=" + this.p.p + "^{" + this.p.pow + "}$ as a proper divisor. Then it is easily verified that $\\left|N_G(P\\cap Q)\\right|$ is at least $" + ptr.data + "$. But then $N_G(P\\cap Q)$ is a subgroup of $G$ of index no more than $" + (this.n.n / ptr.data) + "$. Since $G$ acts transitively on the left cosets of $N_G(P\\cap Q)$ by left multiplication, we have a nontrivial map $\\phi: G\\to S_{" + (this.n.n / ptr.data) + "}$. Contradiction.</p>";
	    this.proofComplete = true;
	    return true;
	}

    },


    //maybe merge this with the element size test? it's kind of the same idea.
    dPTest: function(){
	if(this.proofComplete)
	    return false;
	if(this.p.p + 1 == this.np && this.p.p * (this.np << 1) == this.n.n && this.p.p > 3){
	    this.proofComplete = true;
	    this.proof = "<p>Since $G$ acts transitively on the " + sylow(this.p) + "s of $G$ by conjugation, we have a nontrivial map $\\phi:G\\to S_{" + this.np + "}$. If $P$ is a " + sylow(this.p) + " of $G$, since every element of the normalizer $N_G(P)$ fixes $P$, we in fact have a nontrivial map $\\overline\\phi=\\phi\\mid_{N_G(P)}:N_G(P)\\to S_{" + this.p + "}$. Since $\\left|N_G(P)\\right|=" + (this.p.p << 1) + "$, and the only groups of order $" + (this.p.p << 1) + "$ are $" + zmod(this.p.p << 1) + "$ and $D_{" + this.p + "}$, one of these must be a subgroup of $S_{" + this.p + "}$, which cannot be.</p>";
	    return true;
	}
    }
}
