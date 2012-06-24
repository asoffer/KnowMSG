//implementation of a doubly linked list (with only one sentinal)

function List(){
    this.head = {prev: null, next: null};
    this.head.next = this.head;
    this.head.prev = this.head;

    this.size = 0;
}

List.prototype = {
    toString: function(){
	if(this.size == 0)
	    return "[]";

	var str = "[" + this.head.next.data;
	var ptr = this.head.next;

	while(ptr.next != this.head){
	    ptr = ptr.next;
	    str += ", " + ptr.data;
	}

	return str + "]";
    },

    copy: function(){
	var l = new List();
	var ptr = this.head.next;
	while(ptr != this.head){
	    l.pushBack(ptr.data);
	    ptr = ptr.next;
	}

	return l;
    },

    //add data to the front of the list
    pushFront: function(d){
	++this.size;
	var n = {data: d, prev: this.head, next: this.head.next};
	this.head.next = n;
	n.next.prev = n;
    },


    //add data to the end of the list
    pushBack: function(d){
	++this.size;
	var n = {data: d, prev: this.head.prev, next: this.head};
	this.head.prev = n;
	n.prev.next = n;
    },

    //remove last item in the list and return it
    popFront: function(){
	if(this.size == 0)
	    return;

	d = this.head.next.data;
	this.head.next.next.prev = this.head;
	this.head.next = this.head.next.next;
	--this.size;

	return d;
    },

    //remove last item in the list and return it
    popBack: function(){
	if(this.size == 0)
	    return;

	d = this.head.prev.data;
	this.head.prev.prev.next = this.head;
	this.head.prev = this.head.prev.prev;
	--this.size;
	return d;
    },

    addBefore: function(d, fn){
	var ptr = this.head.next;
	if(ptr != this.head){
	    while(!fn(ptr.data)){
		ptr = ptr.next;
		if(ptr == this.head)
		    return this.pushBack(d);
	    }
	}
	++this.size;
	var n = {data: d, prev: ptr.prev, next: ptr};
	ptr.prev.next = n;
	n.next.prev = n;
    },

    //add data after the first element for which fn returns true
    //or just add at end
    addAfter: function(d, fn){
	var ptr = this.head.next;
	while(!fn(ptr.data)){
	    ptr = ptr.next;
	    if(ptr == this.head)
		return this.pushBack(d);
	}
	++this.size;
	var n = {data: d, prev: ptr, next: ptr.next};
	ptr.next = n;
	n.next.prev = n;
    },

    //the first element in the list
    first: function(){ return this.head.next.data; },

    //the last element in the list
    last: function(){ return this.head.prev.data; },

    //empty the list
    empty: function(){
	this.size = 0;
	this.head.next = this.head;
	this.head.prev = this.head;
    },

    //if data is in the list, remove it otherwise, return null
    remove: function(data){
	var ptr = this.head.next;

	while(ptr != this.head){
	    if(data.equals(ptr.data)){
		ptr.prev.next = ptr.next;
		ptr.next.prev = ptr.prev;

		--this.size;
		
		return data;
	    }

	    ptr = ptr.next;
	}
	return;
    },

    recomputeSize: function(){
	this.size = 0;

	var ptr = this.head.next;
	while(ptr != this.head){
	    ++this.size;
	    ptr = ptr.next;
	}
    },

    //call a function on every element of the list in order
    iterate: function(fn){
	var ptr = this.head.next;
	while(ptr != this.head){
	    fn(ptr.data);
	    ptr = ptr.next;
	}
    },

    //call a function on every element of the list in reverse order
    iterateReverse: function(fn){
	var ptr = this.head.prev;
	while(ptr != this.head){
	    fn(ptr.data)
	    ptr = ptr.prev;
	}
    },

    powerSet: function(){
	var l = new List();

	l.pushBack(new List());
	var ptr = this.head.next;
	while(ptr != this.head){
	    var sz = l.size;

	    for(var i = 0; i < sz; ++i){
		var x = l.popFront();
		var y = x.copy();
		y.pushBack(ptr.data);
		l.pushBack(x);
		l.pushBack(y);
	    }
	    ptr = ptr.next;
	}
	
	return l;
    }

};
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
    }
}

function Prime(n,p,k){
    //pointer back
    this.n = n;

    this.p = p;

    this.pow = k;

    this.np = new List();
    this.proofCount = 0;
    this.proofComplete = false;
}

Prime.prototype = {
    toString: function(){
        return this.p.toString();
    },

    listPowers: function(){
        var l = new List();
        for(var i = 0; i <= this.pow; ++i){
            l.pushBack(p.pow(i));
        }

        return l;
    },

    toStringWithPower: function(){
        if(this.pow == 1)
            return this.p;

        return this.p + "^{" + this.pow + "}";
    },

    incompleteNPSize: function(){
        var c = 0;
        var ptr = this.np.head.next;
        while(ptr != this.np.head){
            if(!ptr.data.proofComplete)
                ++c;
            ptr = ptr.next;
        }

        return c;
    },

    smallestNP: function(){
        var ptr = this.np.head.next;
        while(ptr != this.np.head){
            if(!ptr.data.proofComplete)
                break;
            ptr = ptr.next;
        }

        //what to do if they're all complete?
        return ptr.data;
    },

    prove: function(){
        var ptr = this.np.head.next;

        var flag = false;
        while(ptr != this.np.head){
            var b = ptr.data.proofComplete;
            TechCount.apply(this.n, this, ptr.data);
            TechDNorm.apply(this.n, this, ptr.data);
            TechSymDiv.apply(this.n, this, ptr.data);
            TechNormInSym.apply(this.n, this, ptr.data);
            TechLAI.apply(this.n, this, ptr.data);
            TechLI.apply(this.n, this, ptr.data);
            TechDP.apply(this.n, this, ptr.data);
            TechNC2.apply(this.n, this, ptr.data);
            TechNC.apply(this.n, this, ptr.data);

            flag = flag || (b!=ptr.data.proofComplete);

            ptr = ptr.next;
        }

        ptr = this.np.head.next;
        while(ptr != this.np.head){
            if(!ptr.data.proofComplete)
                return flag;

            ptr = ptr.next;
        }

        this.proofComplete = true;
        return false;
    }
};

function Num(n){
    this.n = n;

    this.primes = new List();

    this.factors = new List();

    if(Math.log(this.n) > 40){
        this.proofComplete = true;
        this.proofShown = true;
        if(sporadicTest(this, true)){
            return;
        }
        else{
            $("#inner_statement").html("<p>Unfortunately the input is to big for me to handle.</p>");
            $("#proof").html("<p></p>");
        }
        return;
    }

    this.factor();

    this.divInject = Number.MAX_VALUE;
    this.smartInject = Number.MAX_VALUE;
    this.needSmart = false;

    //flags and vars for computing and showing proofs
    this.proofComplete = false;
    this.proof = "";
    this.proofShown = false;

    this.workedOptions = new List();
    this.currentLayer = new List();
    this.workedOptions.pushBack(this.currentLayer);
}


Num.prototype = {
    toString: function(){
        return this.n;
    },

    factor: function(){
        if(this.primes.size != 0)
            return;

        var m = this.n;
        var p = 2;
        while(m >= p){
            var pow = 0;
            while(m % p == 0){
                ++pow;
                m /= p;
            }

            if(pow != 0){
                this.primes.pushBack(new Prime(this, p, pow));

            }

            ++p;
        }

    },

    computeFactorList: function(){
        if(this.factors.size != 0)
            return;

        this.factors.pushBack(1);

        var primePtr = this.primes.head.next;
        while(primePtr != this.primes.head){
            var ln = this.factors.size;
            for(i = 0; i < ln; ++i){
                var x = this.factors.popFront();
                for(var j = 0; j <= primePtr.data.pow; ++j){
                    this.factors.pushBack( x * Math.pow(primePtr.data.p, j));
                }
            }

            primePtr = primePtr.next;
        }

        this.factors = sort(this.factors);

    },

    kModM: function(k,m){
        this.computeFactorList();

        var l = new List();
        var ptr = this.factors.head.next;
        while(ptr != this.factors.head){
            if(ptr.data % m ==k)
                l.pushBack(ptr.data);
            ptr = ptr.next;
        }

        return l;
    },

    buildNP: function(){
        var ptr = this.primes.head.next;
        while(ptr != this.primes.head){
            var l = this.kModM(1,ptr.data.p);

            var lPtr = l.head.next;

            while(lPtr != l.head){
                ptr.data.np.pushBack(new Option(ptr.data, lPtr.data));

                lPtr = lPtr.next;
            }

            ptr = ptr.next;
        }
    },

    isPrimePower: function(){
        return (this.primes.size == 1);
    },

    isPrime: function(){
        return (this.isPrimePower() && this.primes.first().pow == 1);
    },

    prove: function(){
        if(this.proofComplete)
            return;

        if(TechOne.apply(this) || sporadicTest(this) || TechPrimes.apply(this) || isSimple(this))
            return;

        //compute all the factors and build lists of potential n_p
        this.computeFactorList();
        this.buildNP();

        if(TechSylow.apply(this) || TechTwoOdd.apply(this))
            return;

        //compute the injections
        this.computeInjections();

        if(TechInjectBound.apply(this, this.divInject) || TechInjectBound.apply(this, this.smartInject))
            return;

        //knock off np's too small for a div injection. if we need to
        //do smart injection too. there's a question about wehether
        //this is simpler than some of the other arguments, but it's
        //much easier to do this check once than have some wacky
        //ordering and have to check it 3 different times.
        var ptr = this.primes.head.next;
        while(ptr != this.primes.head){
            while(ptr.data.np.first().np < this.divInject)
                ptr.data.np.popFront();
            while(ptr.data.np.first().np < this.smartInject){
                this.needSmart = true;
                ptr.data.np.popFront();
            }
            ptr = ptr.next;
        }

        //ugly cases
        if(Tech720.apply(this) || Tech840.apply(this) || Tech756.apply(this))
            return;

        var flag = true;
        while(flag && !this.proofComplete){
            flag = false;
            ptr = this.primes.head.prev;
            while(ptr != this.primes.head){
                var b = ptr.data.prove();
                flag = flag || b;

                if(ptr.data.proofComplete){
                    this.proofComplete = true;
                    return;
                }
                ptr = ptr.prev;
            }
            this.currentLayer = new List();
            this.workedOptions.pushBack(this.currentLayer);

        }

        $("#inner_statement").html("<p>There are no simple groups of order " + this + "=" + showFactorization(this) + ".</p>");

    },

    countElements: function(){
        var c = 0;
        var ptr = this.primes.head.next;
        while(ptr != this.primes.head){
            if(ptr.data.pow == 1){
                c += ptr.data.smallestNP().np * (ptr.data.p - 1);
            }
            else
                c += Math.pow(ptr.data.p, ptr.data.pow);
            ptr = ptr.next;
        }

        return c;
    },

    showProof: function(){
        if(this.proofShown)
            return this.proof;

        this.proof += pf_basic(this, this.needSmart);
        var ptr = this.workedOptions.head.next;
        //do all but the last one
        while(ptr != this.workedOptions.head.prev){
            //just dump everything
            var ptr2 = ptr.data.head.next;
            while(ptr2 != ptr.data.head){
                this.proof += "<h6>Case $n_{" + ptr2.data.p +"}=" + ptr2.data.np + "$:</h6>" + ptr2.data.proof;

                ptr2 = ptr2.next;
            }

            ptr = ptr.next;
        }

        var theLastPrime = 0;
        var ptr3 = this.primes.head.prev;
        while(ptr3 != this.primes.head){
            if(ptr3.data.proofComplete){
                theLastPrime = ptr3.data.p;
            }
            ptr3 = ptr3.prev;
        }

        var l = new List();
        ptr2 = ptr.data.head.next;
        while(ptr2 != ptr.data.head){
            if(ptr2.data.p.p == theLastPrime)
                l.pushBack(ptr2.data);
            ptr2 = ptr2.next;
        }

        if(l.size == 1)
            this.proof += l.first().proof;
        else{
            ptr2 = l.head.next;
            while(ptr2 != l.head){
                if(ptr2.data.proof.substr(3,8) == "We first"){
                    this.proof += ptr2.data.proof;
                    break;
                }
                this.proof += "<h6>Case $n_{" + theLastPrime +"}=" + ptr2.data.np + "$:</h6>" + ptr2.data.proof;

                ptr2 = ptr2.next;
            }

        }

        $("#inner_statement").html("<p>There are no simple groups of order $" + this.n + "=" + showFactorization(this) + "$.</p>");

        this.proofShown = true;

        if(this.proofComplete)
            return this.proof;

        var pf = "<div class=\"ui-state-highlight ui-corner-all\" style=\"margin-top: 0px; margin-bottom: 20px; padding: 1em .7em; font-size: 10pt;\"><span class=\"ui-icon ui-icon-info\" style=\"float: left; margin-right: .3em;\"></span><strong>Attention:</strong><br><br>While I cannot find an elementary proof, "
            //try burnside
            if(this.primes.size == 2)
                pf += "Burnside's Theorem tells us that for primes $p$ and $q$, and natural numbers $a$ and $b$, groups of order $p^a\\cdot q^b$ are solvable. Since $" + this.n + "$ is not prime, no group of order $" + this.n + "$ can be simple."

                    //try feit-thompson
            else if(this.n % 2 == 1)
                pf += "the Feit-Thompson Theorem states that all groups of odd order are solvable. Since $" + this.n + "$ is not prime, no group of order $" + this.n + "$ can be simple.";

        //use the classification
            else
                pf += "the classification theorem for finite simple groups tells us the possible sizes of finite simple groups, to which $" + this.n + "$ does not belong.";

        var emel = "asoffer";
        pf += " Below is what I think the beginning of a proof would look like.<br><br>Do you know an elementary technique that would solve this case? <a href = \"mailto:" + emel + "@math.ucla.edu\">Let me know</a>!</div>";
        //var ptr = this.primes.head.next;

        this.proof = pf + this.proof;

        return this.proof;
    },

    computeInjections: function(){
        var m = 0;
        var ptr = this.primes.head.next;

        while(ptr != this.primes.head){
            var guess = Math.floor(ptr.data.pow / (ptr.data.p - 1));

            while(factorialDivisors(guess, ptr.data.p) <= ptr.data.pow)
                ++guess;

            if(factorialDivisors(guess - 1, ptr.data.p) == ptr.data.pow)
                guess -= ptr.data.p;

            if(m < guess)
                m = guess;

            ptr = ptr.next;
        }
        this.divInject = m;


        //WARNING: this is for test that create a normal subgroup of A_n.
        //the method to calculate this.smartInject is sufficient, but we
        //do not guarantee that n > 4 (i.e., we don't guarantee A_n is
        //simple).

        var leftOver = 1;
        var i = 1;
        var n = this.n;
        while(n > 1 && leftOver < (this.divInject << 1)){
            var g = gcd(n, i);
            n /= g;
            leftOver *= i/g;
            ++i;
        }

        this.smartInject = this.divInject;

        if(leftOver >= (this.divInject << 1))
            return;

        ++this.smartInject;
        if(leftOver == 1)
            ++this.smartInject;

    },

    sumOfPrimeDivisors: function(){
        var s = 0;
        var ptr = this.primes.head.next;

        while(ptr != this.primes.head){
            s += ptr.data.p;
            ptr = ptr.next;
        }

        return s;
    },

    //use the chinese remainder theorem
    mustBeCyclic: function(){
        var ptr = this.primes.head.next;

        while(ptr != this.primes.head){
            if(this.kModM(1,ptr.data.p).size != 1 || ptr.data.pow > 1)
                return false;

            ptr = ptr.next;
        }

        return true;
    }

}


//object used to hold information about classes of simple groups
function Simple(nm){
    this.name = nm;
    this.sym = null;
    this.fn = function(n,q){ return 1 };

    //are there any exceptions?
    this.exception = function(n,q){ return false};

    //this variable tells us if it has a determined factorization, or has a product with a variable number of terms
    this.determined = true;
    //if it is totally determined, we can use this to get a very good high guess on where to be looking for the product so we don't have to try lots of products
    this.logBound = 1;
    //if not, use this
    this.powSize = null;
}

Simple.prototype = {
    toString: function(){
        return "[" + this.name + " simple group class]";
    },

    isInstance: function(num){
        if(this.determined){
            var q = Math.floor(Math.pow(num.n, 1/this.logBound)+1);

            while(this.fn(0,q) > num){
                --q;
            }

            if(this.fn(0,q) == num && (new Num(q)).isPrimePower() && !this.exception(0,q)){
                return {q: q, n: 0};
            }
            else
                return false;
        }
        else if(this.powSize == -1){
            var x = this.isThisSize(num);
            if(!x)
                return false;
            if(!this.exception(x.n, x.q))
                return x;
            return false;
        }
        else{
            var l = this.generatePotentialList(num);
            var ptr = l.head.next;
            while(ptr != l.head){
                if(this.fn(ptr.data.n, ptr.data.q) == num && (new Num(ptr.data.q)).isPrimePower() && !this.exception(ptr.data.n,ptr.data.q))
                    return ptr.data;
                ptr = ptr.next;
            }
            return false;

        }

    },

    //only used for undetermined guesses
    generatePotentialList: function(num){
        var ptr = num.primes.head.next;
        var potentials = new List();
        while(ptr != num.primes.head){
            var pow = ptr.data.pow;
            var n = 1;

            while(this.powSize(n) <= pow){
                if(this.powSize(n) > 0 && pow % this.powSize(n) == 0){
                    potentials.pushBack({q: Math.pow(ptr.data.p, pow/this.powSize(n)), n: n});
                }
                ++n;
            }

            ptr = ptr.next;
        }

        return potentials;

    },

}




var simpleA = new Simple("alternating group");
simpleA.sym = function(n,q){ return "A_{" + n + "}"; };
simpleA.determined = false;
simpleA.exception = function(n,q){ return n < 5; };
simpleA.powSize = -1;
simpleA.isThisSize = function(num){
    //fixme, this is really a very dumb way to do it. use newton's method with stirlings formula
    var x = 1;
    var c = 2;
    while(num.n > x){
        ++c;
        x *= c;
    }

    if(num.n == x)
        return {n: c, q: 0};
    return false;
}

var simplePSL = new Simple("projective special linear group");
simplePSL.sym = function(n,q){ return "\\mbox{PSL}_{" + n + "}(" + q + ")"; };
simplePSL.determined = false;
simplePSL.exception = function(n,q){ return (n == 2 && (q == 2 || q == 3)); };
simplePSL.powSize = function(num){ return triangle(num - 1); };
simplePSL.fn = function(n,q){
    var x = 1;
    for(i = 2; i <= n; ++i)
        x *= Math.pow(q, i) - 1;

    return x * Math.pow(q, this.powSize(n))/gcd(n, q - 1);
}

var simpleO = new Simple("orthogonal group");
simpleO.sym = function(n,q){ return "B_{" + n + "}(" + q + ")"; };
simpleO.determined = false;
simpleO.exception = function(n,q){ return (((n == 2) && (q == 2)) || (n == 1)); };
simpleO.powSize = function(num){ return Math.pow(num, 2); };
simpleO.fn = function(n,q){

    var x = 1;
    for(i = 1; i <= n; ++i){
        x *= Math.pow(q, 2*i) - 1;
    }

    return x * Math.pow(q, this.powSize(n))/gcd(2, q - 1);
}

var simplePSp = new Simple("projective symplectic group");
simplePSp.sym = function(n,q){ return "\mbox{PS}p_{" + (2*n) + "}(" + q + ")"; };
simplePSp.determined = false;
simplePSp.exception = function(n,q){ return n < 3; };
simplePSp.powSize = function(num){ return num * num; };
simplePSp.fn = function(n,q){
    var x = 1;
    for(i = 1; i <= n; ++i){
        x *= Math.pow(q, 2 * i) - 1;
    }

    return x * Math.pow(q, this.powSize(n))/gcd(2, q - 1);
}

var simpleOp = new Simple("orthogonal group");
simpleOp.sym = function(n,q){ return "O_{" + (2*n) + "}^+(" + q + ")"; };
simpleOp.determined = false;
simpleOp.exception = function(n,q){ return n < 4; };
simpleOp.powSize = function(num){ return num * (num - 1); };
simpleOp.fn = function(n,q){
    var x = 1;
    for(i = 1; i < n; ++i){
        x *= Math.pow(q, i * 2) - 1;
    }

    return  x * Math.pow(q, this.powSize(n)) * (Math.pow(q, n) - 1)/gcd(4, Math.pow(q,n) - 1);
}

var simpleE6 = new Simple("exceptional Chevalley group");
simpleE6.sym = function(n,q){ return "E_6(" + q + ")"; };
simpleE6.fn = function(n,q){ return Math.pow(q, 36) *
    (Math.pow(q, 12) - 1) *
        (Math.pow(q, 9) - 1) *
        (Math.pow(q, 8) - 1) *
        (Math.pow(q, 6) - 1) *
        (Math.pow(q, 5) - 1) *
        (Math.pow(q, 2) - 1) /
        gcd(3, q - 1);
};
simpleE6.logBound = 78;

var simpleE7 = new Simple();
simpleE7.name = "exceptional Chevalley group";
simpleE7.sym = function(n,q){ return "E_7(" + q + ")"; };
simpleE7.fn = function(n,q){ return Math.pow(q, 63) *
    (Math.pow(q, 18) - 1) *
        (Math.pow(q, 14) - 1) *
        (Math.pow(q, 12) - 1) *
        (Math.pow(q, 10) - 1) *
        (Math.pow(q, 8) - 1) *
        (Math.pow(q, 6) - 1) *
        (Math.pow(q, 2) - 1) /
        gcd(2, q - 1);
};
simpleE7.logBound = 133;

var simpleE8 = new Simple();
simpleE8.name = "exceptional Chevalley group";
simpleE8.sym = function(n,q){ return "E_8(" + q + ")"; };
simpleE8.fn = function(n,q){ return Math.pow(q, 120) *
    (Math.pow(q, 30) - 1) *
        (Math.pow(q, 24) - 1) *
        (Math.pow(q, 20) - 1) *
        (Math.pow(q, 18) - 1) *
        (Math.pow(q, 14) - 1) *
        (Math.pow(q, 12) - 1) *
        (Math.pow(q, 8) - 1) *
        (Math.pow(q, 2) - 1); };
simpleE8.logBound = 248;

var simpleF4 = new Simple();
simpleF4.name = "exceptional Chevalley group";
simpleF4.sym = function(n,q){ return "F_4(" + q + ")"; };
simpleF4.fn = function(n,q){ return Math.pow(q, 24) * (Math.pow(q, 12) - 1) * (Math.pow(q, 8) - 1) * (Math.pow(q, 6) - 1) * (Math.pow(q, 2) - 1); };
simpleF4.logBound = 52;

//FIXME the exception is when q=2, and then it has a simple subgroup of index 2. is this part of the classification, or are those cases found by something else? hopefully it's the latter, but i may need to fix that
var simpleG2 = new Simple();
simpleG2.name = "exceptional Chevalley group";
simpleG2.sym = function(n,q){ return "G_2(" + q + ")"; };
simpleG2.fn = function(n,q){ return Math.pow(q, 6) * (Math.pow(q, 6) - 1) * (Math.pow(q, 2) - 1); };
simpleG2.logBound = 14;
simpleG2.exception = function(n,q){ return (q == 2); };

var simple2A = new Simple("projective special unitary group");
simple2A.sym = function(n,q){ return "\\mbox{PSU}_{" + (n+1) + "}(" + q + ")"; };
simple2A.determined = false;
simple2A.exception = function(n,q){ return ((n == 2 && q == 2) || n ==1); };
simple2A.powSize = function(num){ return triangle(num); };
simple2A.fn = function(n,q){
    var x = 1;
    for(i = 1; i <= n; ++i)
        x *= Math.pow(q, i+1) + Math.pow(-1, i);

    return x * Math.pow(q, this.powSize(n))/gcd(n + 1, q + 1);
}

var simpleOm = new Simple("twisted Chevalley group");
simpleOm.sym = function(n,q){ return "\\mbox{O}_{" + (2*n) + "}^-(" + q + ")"; };
simpleOm.determined = false;
simpleOm.exception = function(n,q){ return n < 4; };
simpleOm.powSize = function(num){ return 2*triangle(num - 1); };
simpleOm.fn = function(n,q){

    var x = 1;
    for(i = 1; i < n; ++i)
        x *= Math.pow(q, 2*i) -1;

    return x * (Math.pow(q,n) + 1) * Math.pow(q, this.powSize(n))/gcd(4, Math.pow(q,n) + 1);
}

var simple2E6 = new Simple();
simple2E6.name = "Steinberg group";
simple2E6.sym = function(n,q){ return "{}^2E_6(" + q + "^2)"; };
simple2E6.fn = function(n,q){ return Math.pow(q, 36) *
    (Math.pow(q, 12) - 1) *
        (Math.pow(q, 9) + 1) *
        (Math.pow(q, 8) - 1) *
        (Math.pow(q, 6) - 1) *
        (Math.pow(q, 5) + 1) *
        (Math.pow(q, 2) - 1) /
        gcd(3, q + 1); };
simple2E6.logBound = 78;

var simple3D4 = new Simple();
simple3D4.name = "Steinberg group";
simple3D4.sym = function(n,q){ return "{}^3D_4(" + q + "^3)"; };
simple3D4.fn = function(n,q){ return Math.pow(q, 12) *
    (Math.pow(q, 6) - 1) *
        (Math.pow(q, 2) - 1) *
        (Math.pow(q, 8) + Math.pow(q,4) + 1); };

simple3D4.logBound = 28;

//these cases are odd. we use q when we mean to use n
var simpleSuz = new Simple();
simpleSuz.name = "Suzuki group";
simpleSuz.exception = function(n,q){ return ((this.nn - 1) << 1) < 1; };
simpleSuz.sym = function(n,q){ return "Sz(2^{" + this.nn + "})"; };
simpleSuz.fn = function(n,q){ 
    //for saving n;
    this.nn = Math.log(q)/Math.log(2);

    if(this.nn != Math.floor(this.nn))
        return -1;

    return Math.pow(q, 2) *
        (Math.pow(q, 2) + 1) *
        (q - 1);
};
simpleSuz.logBound = 5;

var simpleRee2 = new Simple();
simpleRee2.name = "Ree group";
simpleRee2.exception = function(n,q){ return this.nn < 1; };
simpleRee2.sym = function(n,q){ return "{}^2F_4(2^{" + this.nn + "})"; };
simpleRee2.fn = function(n,q){ 
    //for saving n;
    this.nn = Math.log(q)/Math.log(2);

    return Math.pow(q, 12) *
        (Math.pow(q, 6) + 1) *
        (Math.pow(q, 4) - 1) *
        (Math.pow(q, 3) + 1) *
        (q - 1);
};
simpleRee2.logBound = 26;

var simpleRee3 = new Simple();
simpleRee3.name = "Ree group";
simpleRee3.exception = function(n,q){ return this.nn < 3; };
simpleRee3.sym = function(n,q){ return "{}^2G_2(3^{" + this.nn + "})"; };
simpleRee3.fn = function(n,q){ 
    //for saving n;
    this.nn = Math.log(q)/Math.log(3);

    return Math.pow(q, 3) *
        (Math.pow(q, 3) + 1) *
        (q - 1);
};
simpleRee3.logBound = 7;

//to catch the derived subgroup of the 2F4 Ree groups
var simpleTits = new Simple();
simpleTits.name = "Tits group, ${}^2F_4(2)'$, which is the derived subgroup of (and has index $2$ in) the Ree group ${}^2F_4(2)$";
//simpleTits.sym = function(n,q){ return ""; };
simpleTits.determined = false;
simpleTits.powSize = -1;
simpleTits.isThisSize = function(num){
    if(num == 17971200)
        return {n: 0, q: 0};
}

//------------------------------

//we wont include primes, because they are taken care of elsewhere. they're much easier
var simpleArray = new Array(simpleA, simplePSL, simpleO, simplePSp, simpleOp, simpleE6, simpleE7, simpleE8, simpleF4, simpleG2, simple2A, simpleOm, simple2E6, simple3D4, simpleSuz, simpleRee2, simpleRee3, simpleTits);

function isSimple(n){
    var simpleList = new List();
    for(var i = 0; i < simpleArray.length; ++i){
        var x = simpleArray[i].isInstance(n);
        if(x){
            var s = "he " + simpleArray[i].name;
            if(simpleArray[i].sym != null)
                s += " $" + simpleArray[i].sym(x.n, x.q) + "$";
            s += ".</p>";

            simpleList.pushBack(s);
        }
    }

    if(simpleList.size == 0)
        return false;

    n.proofComplete = true;
    n.proofShown = true;

    $("#inner_statement").html("<p>There is a simple groups of order $" + n + "=" + showFactorization(n) + "$.</p>");

    this.proof = "";

    if(simpleList.size == 1){
        n.proof = "<p>Up to isomorphism, the only simple group of order $" + n + "$ is t" + simpleList.first();
        return true;
    }

    n.proof = "<p>The following are all of the simple groups of order $" + n + "$ up to isomorphism. Some of these groups may be isomorphic, but every simple group of order $" + n + "$ is isomorphic to at least one of the following:</p>";

    var ptr = simpleList.head.next;
    while(ptr != simpleList.head){
        n.proof += "<p>T" + ptr.data;

        ptr = ptr.next;
    }


    return true;
}

//------------------------------
var spor = new Array("7920", "95040", "443520", "10200960", "244823040", "175560", "604800", "50232960", "86775571046077562880", "4157776806543360000", "42305421312000", "495766656000", "64561751654400", "4089470473293004800", "1255205709190661721292800", "44352000", "898128000", "4030387200", "145926144000", "448345497600", "460815505920", "273030912000000", "51765179004000000", "90745943887872000", "4154781481226426191177580544000000", "808017424794512875886459904961710757005754368000000000");
var spor_sym = new Array("M_{11}","M_{12}", "M_{22}", "M_{23}", "M_{24}", "J_1", "J_2", "J_3", "J_4", "Co_1", "Co_2", "Co_3", "Fi_{22}", "Fi_{23}", "Fi_{24'}", "HS", "McL", "He", "Ru", "Suz", "O'N", "HN", "Ly", "Th", "B", "M");

var spor_name = new Array("a Mathieu group","a Mathieu group","a Mathieu group","a Mathieu group","a Mathieu group","a Janko group","a Janko group","a Janko group","a Janko group","a Conway group","a Conway group","a Conway group","a Fischer Group","a Fischer Group","a Fischer Group","the Higman-Sims group","the McLaughlin group","the Held group","the Rudvalis group","the Suzuki sporadic group","the O'Nan group","the Harada-Norton group","the Lyons group","the Thompson group","the Baby Monster group","the Fischer-Griess Monster, or the monster group");


function sporadicTest(num, b){
    if(b === undefined)
        b = false;

    if(b)
        num.n = GLOBAL_str_n;

    for(var i = 0; i < spor.length; ++i){
        if((""+num.n) == spor[i]){
            $("#inner_statement").html("<p>There exists a simple group of order $" + num + (b ? "" : "=" + showFactorization(num)) + "$.</p>");

            num.proof = "<p>In fact, the sporadic group $" + spor_sym[i] + "$, (" + spor_name[i] + ") has order $" + num.n + "$.</p>";
            num.proofShown = true;
            num.proofComplete = true;
            return true;
        }
    }

    return false;
}

function zmod(n){
    return "\\mathbb{Z}/" + n.toString() + "\\mathbb{Z}";
}

function sort(l){
    var l2 = new List();

    var ptr = l.head.next;

    while(ptr != l.head){
        l2.addBefore(ptr.data, function(x){ return (x >= ptr.data); });
        ptr = ptr.next;
    }

    return l2;
}

function factorial(n){
    if(n <= 0)
        return 1;
    return n * factorial(n - 1);
}

function triangle(n){
    return ((n * (n + 1))/2);
}

function gcd(a,b){
    if(a * b == 0)
        return a + b;

    if(a < b)
        return gcd(b,a);

    return gcd(b, a % b);
}

function toList(l,force){
    //return the string, but also a boolean telling us if the line is long
    var b = false;
    var s = "\\{";

    var ptr = l.head.next;
    var sz = 0;
    while(ptr != l.head){
        sz += ("" + ptr.data).length;

        if(sz > 40){
            s += "$$ $$";
            sz = 0;
        }

        s += ptr.data + ", ";
        ptr = ptr.next;
    }

    s = s.substr(0,s.lastIndexOf(",")) + "\\}";

    if(s.length > 80 && !force){
        s = "\\{" + l.first() + ",\\dots," + l.last() + "\\}";
        b = true;
    }

    return {s: s, b: b};
}

function inOrIs(e,l,force){
    //return the string, but also a boolean telling us if the line is long

    if(l.size == 1)
        return {s: (e + "=" + l.first()), b: false};

    var tl = toList(l, force);

    return {s: e + "\\in " + tl.s, b: tl.b};
}

function toEnglishCentered(l, force, toPass){
    if(l.size == 1)
        return "$$" + l.first() + "$$";
    if(l.size == 2)
        return "$$" + l.first() + "\\mbox{ and }" + l.last() + ",$$";

    var s = "$$";

    var ptr = l.head.next;

    var sz = 0;
    while(ptr != l.head.prev){
        sz += ("" + ptr.data).length;
        if(sz > 40){
            s += "$$ $$";
            sz = 0;
        }

        s += ptr.data + ", ";
        ptr = ptr.next;
    }

    s+= "\\mbox{ and }" + l.last() + "$$";
    if(s.length > 80){
        if(!force)
            s = "<span id = \"0:" + toPass + "\" class = \"list\" title = \"Expand this list\">$$" + l.first() + ",\\dots," + l.last() + "$$</span>";
        else
            s = "<span id = \"1:" + toPass + "\" class = \"list\" title = \"Expand this list\">" + s + "</span>";
    }


    return s;
}

function showFactorization(n){
    var str = "";

    var ptr = n.primes.head.next;
    while(ptr != n.primes.head){
        str += ptr.data.p;
        if(ptr.data.pow > 1)
            str += "^{" + ptr.data.pow + "}"
                if(ptr.next != n.primes.head)
                    str += "\\cdot";
        ptr = ptr.next;
    }
    return str;
}

//returns the number of times n! is divisible by the prime p. assumes that p is prime.
function factorialDivisors(n,p){
    var m = n;
    var c = 0;
    while(m > 1){
        m /= p;
        c += Math.floor(m);
    }

    return c;
}

function recursiveEGCD(a,b){
    if(a == 0)
        return {g: b, y: 0, x: 1};

    var v = recursiveEGCD(b % a, a);
    return {g: v.g, y: v.x - Math.floor(b / a) * v.y, x: v.y};
}

function modInverse(a,m){

    var v = recursiveEGCD(a,m);
    if(v.g != 1)
        return false;
    else
        return (m + v.y) % m;
}

//look for an element of order o in A_a
//this is only used for elements of order p*q, thus far, so i'll only code it to do that FIXME
function findElementInAlt(o,a){
    var x = new Num(o);
    x.factor();
    var p1 = x.primes.first().p;
    var p2 = x.primes.last().p;

    //make it even
    if(p1 == 2)
        p1 = 4;

    if(p1 * p2 < a)
        return true;

    var p1i = modInverse(p1,p2);
    var p2i = modInverse(p2,p1);


    var y = (p1i * a) % p2;
    var z = (p2i * a) % p1;

    if(y == 0 || z == 0)
        return false;

    return y * p1 + z * p2 == a;
}

function sylow(p){
    return "Sylow $" + p + "$-subgroup";
}

function pf_let(n){
    return "Let $G$ be a group of order $" + n + "$. ";
}

pf_contradiction = "Assume for the sake of contradiction that $G$ is simple. ";

function pf_prime(p){
    return "<p>" + pf_let(p) + "Lagrange's theorem tells us that the order of every subgroup group of $G$ divides $" + p + "$. Since $" + p + "$ is prime, the only subgroups are the trivial group and $G$ itself, so these are the only normal subgroups as well. Hence, $G$ is simple.</p><p>Moreover, up to isomorphism, the only group of order $" + p + "$ is the cyclic group $" + zmod(p) + "$.</p>";
}

function pf_prime_power(p,ppow){
    return "<p>" + pf_let(ppow) + "By the class equation, $$\\left|G\\right|=\\left|Z(G)\\right|+\\sum_{g\\in O^*}[G:C_G(g)].$$ Since $\\left|G\\right|$ is divisible by $" + p + "$, as is the sum, it follows that $\\left|Z(G)\\right|$ is divisible by $" + p + "$. So either $Z(G)=G$, meaning $G$ is abelian and therefore not simple, or $Z(G)\\lhd G$.</p>"
}

function pf_one_mod_p(n,p){
    var textPow = "";
    if(p.pow > 1)
        textPow += "^{" + p.pow + "}";

    var index = new Num(n.n / Math.pow(p.p, p.pow));
    index.computeFactorList();

    return "<p>" + pf_let(n) + "From the Sylow theorems, we know that the number of " + sylow(p) + "s of $G$ must be congruent to $1$ modulo $" + p + "$ and divide the index $[G:P]$, where $P$ is any " + sylow(p) + " of $G$. We calculate the index as $[G:P]=" + n + "/" + p + textPow + "=" + index + "$. The divisors of $" + index + "$ are " + toEnglishCentered(index.factors, false, "f_" + index) + "of which, only $1$ is congruent to $1$ modulo $" + p + "$.</p><p>We also know from the Sylow theorems that the " + sylow(p) + "s of $G$ conjugate to each other. Since there is only one " + sylow(p) + ", $P$, for each $g\\in G$, $g^{-1}Pg=P$. That is, $P\\lhd G$, so there are no simple groups of order $" + n + "$.</p>";
}

function pf_div_inject(n){
    return "<p>" + pf_let(n) + pf_contradiction + "Notice that $" + n + "$ does not divide $" + (n.divInject - 1) + "!$, so any map from $G$ to $S_{" + (n.divInject - 1) + "}$ cannot be injective. Since for any map $\\psi:G\\to S_n$, we have that $\\ker\\psi\\unlhd G$, there can be no such non-trivial map for $n&lt;" + n.divInject + "$.</p>";
}

function pf_smart_inject(n){
    var ind = factorial(n.smartInject - 1)/n.n;
    var an = "A_{" + (n.smartInject - 1) + "}";
    var sn = "S_{" + (n.smartInject - 1) + "}";

    var pf = pf_div_inject(n) + "<p>Furthermore, if we have a map $\\psi:G\\to S_{" + (n.smartInject - 1) + "}$, it cannot be an injection. If it were, let $H=\\psi(G)\\le G$. Notice that $H$ has index $" + ind + "$ in $" + sn + "$.";

    if(ind % 2 == 1)
        pf += " Then $H$ cannot be a subgroup of $" + an + "$ lest it have index $" + (ind >> 1) + ".5$ in $" + an + "$.";
    else
        pf += " If $H\\le " + an + "$, then $[" + an + ":H]=" + (ind >> 1) + "$. Since, $" + an + "$ acts transitively on the cosets of $H$ in $" + an + "$, we have a nontrivial map $\\psi:" + an + "\\to S_{" + (ind >> 1) + "}$. The kernel of this map is a proper normal subgroup of $" + an + "$. Since this map cannot be injective for divisibility reasons, its existence contradicts the simplicity of $A_{" + (n.smartInject - 1) + "}$.";
    return pf + "</p><p>On the other hand, if $H\\not\\le " + an + "$, since $" + an + "\\lhd " + sn + "$, it follows that, $1 &lt; " + an + "\\cap H\\lhd " + sn + "\\cap H=H\\cong G$, contradicting the simplicity of $G$. Thus, any non-trivial map from $G$ into a symmetric group $S_n$ must in fact have $n\\ge" + n.smartInject + "$.</p>";
}

function pf_inject(n,p){
    var pf = "";
    var i;

    if(p.np.last().np >= n.divInject){
        pf += pf_smart_inject(n);
        i = n.smartInject;
    }
    else{
        pf += pf_div_inject(n);
        i = n.divInject;
    }

    var pow = "";
    if(p.pow != 1)
        pow = "^{" + p.pow + "}";
    var index = n.n/Math.pow(p.p, p.pow);

    return pf + "<p>From the Sylow theorems, we know that the number of Sylow " + p + "-subgroups of $G$ must be congruent to $1$ modulo " + p + " and divide the index $[G:P]$, where $P\\ $ is any " + sylow(p) + " of $G$. We calculate the index as $[G:P]=" + n + "/" + p.p + pow + "=" + index + "$. The divisors of $" + index + "$ which are congruent to $1$ modulo $" + p + "$ are " + toEnglishCentered(n.kModM(1,p.p), false, "CAN'T MATTER") + "</p><p>Since $G$ acts on the " + sylow(p) + "s transitively by conjugation, we have a nontrivial map $\\phi:G\\to S_{n_{" + p + "}}$ where $n_{" + p + "}$ denotes the number of " + sylow(p) + "s of $G$. But we know that $n_{" + p + "}\\le " + n.kModM(1,p.p).last() + "$. Since $G$ cannot inject into any permutation group $S_n$ for $n&lt;" + i + "$, we know that $\\ker\\phi\\ne 1$. Because the action of $G$ is transitive, $\\ker\\phi\\ne G$. Then we have the nontrivial normal subgroup $\\ker\\phi\\lhd G$. Contradiction.</p>";
}


function pf_basic(n, b){
    var pf = "";

    //b is a flag to tell us which injection proof to take
    if(b)
        pf += pf_smart_inject(n);
    else
        pf += pf_div_inject(n);

    pf += "<p>We also know from the Sylow theorems that for each prime $p$, the number of Sylow $p$-subgroups of $G$ must be congruent to $1$ modulo $p$ and divide the index $[G:P]$, where $P$ is any Sylow $p$-subgroup of $G$. Moreover, $G$ acts on the Sylow $p$-subgroups transitively by conjugation, so we get a map $\\phi_p:G\\to S_{n_p}$, where $n_p$ denotes the number of Sylow $p$-subgroups of $G$. Then we know that for each prime $p$ dividing $\\left|G\\right|$, $n_p\\ge";
    if(b)
        pf += n.smartInject;
    else
        pf += n.divInject;
    pf+= "$. Therefore," + sylowList(n);

    return pf;
}

function sylowList(n){
    var pf = "";
    var ptr = n.primes.head.next;

    while(ptr != n.primes.head.prev){
        var ioi = inOrIs("n_{" + ptr.data.p + "}", ptr.data.np, false);

        if(ioi.b)
            pf += "<span id = \"0:n_" + ptr.data.p + "\" class = \"list\" title = \"Expand this list\">$$" + ioi.s + ",$$</span>";
        else
            pf += "$$" + ioi.s + ",$$";
        ptr = ptr.next;
    }

    ioi = inOrIs("n_{" + ptr.data.p + "}", ptr.data.np, false);
    if(ioi.b)
        pf += "<span id = \0:n_" + ptr.data.p + "\" class = \"list\" title = \"Expand this list\">$$\\mbox{and }" + ioi.s + ".$$</span>";
    else
        pf += "$$\\mbox{and }" + ioi.s + ".$$</p>";

    return pf;
}

var GLOBAL_v = 1.4;
var GLOBAL_d = "June 23, 2012";
var GLOBAL_n = null;
var GLOBAL_fail = new Array(1008,1040,1080,1140,1224,1232);

$(function(){
    //set the version number
    $("#version").html("<span id = \"vers\">Version " + GLOBAL_v + "</span><br>Last updated "+GLOBAL_d);
    $("#vers").click(function(){
        sendMessage("Changes","<h4>What's new in Version " + GLOBAL_v + "?</h4><ul><li>All orders solved below $1000$.</li><li>Older techniques strengthened.</li><li>Some display issues fixed.</li></ul><h4>What's new in Version 1.3?</h4><ul><li>Groups sizes $540, 630, 810, 990, 1890$ and more solved.</li><li>Several bugs fixed.</li></ul><h4>What's new in Version 1.2?</h4><ul><li>Display issues with long lists fixed.</li><li>Potentially long lines only displayed at users choice.</li><li>Added capability to input arithmetic expressions.</li></ul>");
    });

    generateFailList();

    //set the information about NoMSG
    $("#about")
    .button({icons: {primary: "ui-icon-info"}})
    .click(function(){
        sendMessage("About NoMSG", "<h4>What is NoMSG?</h4><p>NoMSG is a proof generator. If you input a positive integer $n$, NoMSG will attempt to find a simple group of order $n$, or generate a proof that no such simple groups exist.</p><h4>How does it work?</h4><p>Magic. But if you want to know more, read about it <a href = \"http://soffer801.wordpress.com/2012/06/23/nomsg-v1-4/\">here</a>.</p><h4>Where did the information come from?</h4><p>Most of the information to construct these proofs can be found on <a href=\"http://en.wikipedia.org/wiki/Sylow_theorems#Fusion_results\">Wikipedia</a>, or any introductory group theory text. For some of the more involved proofs, I adapted proofs from these sources:</p><ul><li>Guillermo Mantilla's <a href = \"http://www.math.wisc.edu/~jensen/Algebra/ThmsGroups.pdf\">notes</a> on group theory.</li><li>Posts from the blog <a href =\"http://crazyproject.wordpress.com/tag/simple-group/\">Project Crazy Project</a>.</li><li><a href = \"http://en.wikipedia.org/wiki/List_of_finite_simple_groups\">This list</a> from Wikipedia.</li></ul><p>and puns on the <a href = \"\">splash page</a> from this friend:</p><ul><li><a href = \"http://www.math.ucla.edu/~jedyang/\">Jed Yang</a></li></ul>");
    });

//------------------------------

$("#number_in").keyup(function(e){
    if(e.keyCode == 13)
    $("#go").click();
});

    $("#go")
.button()
    .click(function() {
        var v = $("#number_in").val();
        for(var i = 0; i < v.length; ++i){
            var x = v[i].charCodeAt(0);
            if(x < 40 || x == 44 || x > 57){
                $("#proof").html("<div class=\"ui-widget\"><div class=\"ui-state-error ui-corner-all\"><span class=\"ui-icon ui-icon-alert\" style=\"float: left; margin-right: .3em;\"></span><strong>Error: </strong>I don't think \"" + v + "\" is a number." + (x == 94? "This might be because I can't do exponentiation, and you used \"^.\" Sorry to disappoint.":" Please try again, with something slightly more \"numbery.\"") + "</div></div>");
                return;
            }
        }

        try{
            var x = eval(v);

        }
        catch(e){
            $("#proof").html("<div class=\"ui-widget\"><div class=\"ui-state-error ui-corner-all\"><span class=\"ui-icon ui-icon-alert\" style=\"float: left; margin-right: .3em;\"></span><strong>Error: </strong>Your input was invalid. I'm not exactly sure why, but you probably messed something up. Try again without messing up this time.</div></div>");
            return;
        }

        var y = Math.floor(x);

        if(y != x || x < 1){
            $("#inner_statement").html("<p>There are no (simple) groups of order $" + x + "$.</p>");

            $("#proof").html("<div class=\"ui-widget\"><div class=\"ui-state-error ui-corner-all\"><span class=\"ui-icon ui-icon-alert\" style=\"float: left; margin-right: .3em;\"></span><strong>Error: </strong>Your input was not a positive integer. Please try again, with a number that has a more \"positive integer\" vibe to it.</div></div>");

            MathJax.Hub.Typeset();

            return;
        }

        solve(x);
        setListExpandDisplay();
    });

/*
//for testing
var x = 800000;
var counter = new List();
while(x <= 800000){
    x+=1;
    GLOBAL_n = new Num(x);
    GLOBAL_n.prove();
    if(!GLOBAL_n.proofComplete){
        //console.log(GLOBAL_n.n);
        counter.pushBack(GLOBAL_n.n);
    }
}

console.log("" + counter);
*/
});

function solve(x){
    GLOBAL_str_n = $("#number_in").val();
    GLOBAL_n = new Num(x);

    GLOBAL_n.prove();
    $("#proof").html(GLOBAL_n.showProof());

    MathJax.Hub.Typeset();
}

function setListExpandDisplay(){
    //set expanding ability
    $("span.list").click(function(){
        var b = parseInt(this.id.split(":")[0]);
        var x = this.id.split(":")[1].split("_")[0];
        var p = parseInt(this.id.split("_")[1]);

        //find the right prime
        var ptr = GLOBAL_n.primes.head.next;
        while(ptr != GLOBAL_n.primes.head){
            if(ptr.data.p == p)
        break;
    ptr = ptr.next;
        }

        if(x == "n")
        $(this).html("$$" + inOrIs("n_{" + ptr.data.p + "}", ptr.data.np, (b == 0)).s + "$$");

        else if(x == "f"){
            var ind = new Num(p);
            ind.computeFactorList();
            var s = toEnglishCentered(ind.factors, (b == 0));
            $(this).html(s.split(">")[1].split("<")[0]);
        }

        this.id = "" + (1 - b) + ":"+this.id.split(":")[1];
        MathJax.Hub.Typeset();
    });
}

function setDialog(title){
    $("#message").dialog({
        width: 400,
    resizable: false,
    autoOpen: false,
    modal: true,
    open: function(){
        $('.ui-widget-overlay').hide().fadeIn();
    },
    hide: "fade",
    title: title
    });

}

function sendMessage(title, message){
    $("#message").html(message);
    setDialog(title);
    $("#message").dialog("open");
    MathJax.Hub.Typeset();
}

function generateFailList(){
    var s = "Smallest inadequate proofs: $\\left|G\\right|=$";
    for(var i = 0; i < 5; ++i)
        s += "<span style = \"cursor:pointer;\" onClick=\"solve(" + GLOBAL_fail[i] + ")\">$" + GLOBAL_fail[i] + "$</span>$,$";
    s += "<span style = \"cursor:pointer;\" onClick=\"solve(" + GLOBAL_fail[i] + ")\">$" + GLOBAL_fail[i] + "$</span>$\\dots$";

    $("table td").first().html(s);
}

//DISPLAY CODES:
//0 there are no simple groups of order n
//1 there is a simple group of order n
//2 every group of order n is simple
//3 there are no (simple) groups of order n
function Technique(str, b, dc){
    if(b === undefined)
        b = false;
    if(dc === undefined)
        dc = 0;

    this.simpleType = b;
    this.test = function(n, p, np){ return false; }
    this.getProof = function(n, p, np){ return ""; }
    this.displayCode = dc;
}

Technique.prototype = {
    //try to eliminate the option, if you can, save the proof. return whether or not you did anything
    apply: function(n, p, np){
        if(this.simpleType)
            np = n;

        //if it's already been solved, don't try again
        if(np.proofComplete)
            return false;

        if(this.test(n, p, np)){
            np.proofComplete = true;
            np.proof = this.proof(n, p, np);

            n.currentLayer.pushBack(np);

            if(this.simpleType){
                var v = $("#inner_statement");
                switch(this.displayCode){
                    case 0:
                        v.html("<p>There are no simple groups of order $" + n + "=" + showFactorization(n) + "$.</p>");
                        break;
                    case 1:
                        v.html("<p>There is a simple group of order $" + n + "$.</p>");
                        break;
                    case 2:
                        v.html("<p>Every group of order $" + n + "$ is simple.</p>");
                        break;
                    case 3:
                        v.html("<p>There are no (simple) groups of order $" + n + "$.</p>");
                        break;
                    default:
                        v.html("<p>What the hell kind of question is that?.</p>");
                }

                n.proofShown = true;

            }
            return true;
        }

        return false;
    }
}

TechDP = new Technique("dihedral p test");
TechDP.test = function(n, p, np){
    return ((p.p + 1 == np) && (p.p * (np << 1) == n.n) && (p.p > 3));
}
TechDP.proof = function(n, p, np){
    return "<p>Since $G$ acts transitively on the " + sylow(p) + "s of $G$ by conjugation, we have a non-trivial map $\\phi:G\\to S_{" + np + "}$. If $P$ is a " + sylow(p) + " of $G$, since every element of the normalizer $N_G(P)$ fixes $P$, we in fact have a non-trivial map $\\overline\\phi=\\phi\\mid_{N_G(P)}:N_G(P)\\to S_{" + p + "}$. Since $\\left|N_G(P)\\right|=" + (p.p << 1) + "$, and the only groups of order $" + (p.p << 1) + "$ are $" + zmod(p.p << 1) + "$ and $D_{" + p + "}$, one of these must be a subgroup of $S_{" + p + "}$, which cannot be.</p>";
}

TechLI = new Technique("large intersection");
TechLI.test = function(n, p, np){
    if(p.pow == 1 || np % Math.pow(p.p, 2) == 1)
        return false;

    //we're looking for  divisors of p^a that are larger than p^(a+1)
    var f = n.kModM(0, Math.pow(p.p, p.pow));
    np.ptr = f.head.prev;

    while(np.ptr.data > Math.pow(p.p, p.pow + 1))
        np.ptr = np.ptr.prev;

    np.ptr = np.ptr.next;
    np.exp = "";
    if(p.pow > 2)
        np.exp = "^{" + (p.pow - 1) + "}";
    //now we know there are two sylow subgroups with large intersection.
    //both p and q are in the normalize of their intersection
    return (n.n/ np.ptr.data < n.divInject);
}
TechLI.proof = function(n, p, np){
    return "<p>Since $n_{" + p + "}\\not\\equiv 1(\\bmod" + p + "^2)$, there must be two distinct " + sylow(p) + "s of $G$, $P$ and $Q$, such that $[P:P\\cap Q]&lt; p^2$. As this index must be a power of $" + p + "$, and $P\\ne Q$, the index must be $" + p + "$. That is, $\\left|P\\cap Q\\right|=" + p + np.exp + "$.</p><p>However, $P\\cap Q$ is a $" + p + "$-subgroup of $P$ with index divisible by $" + p + "$, so $" + p + "$ divides $[N_P(P\\cap Q):P\\cap Q]$, meaning $N_P(P\\cap Q)=P$. This means, $P\\cap Q\\lhd P$, so $P\\le N_G(P\\cap Q)$. Similarly, $Q\\le N_G(P\\cap Q)$, so $PQ\\subseteq N_G(P\\cap Q)$. We can therefore bound the size of the normalizer by $$\\left|N_G(P\\cap Q)\\right|\\ge\\left|PQ\\right|=\\frac{\\left|P\\right|\\cdot\\left|Q\\right|}{\\left|P\\cap Q\\right|}=" + p + "^{" + (p.pow + 1) + "}.$$ We also know that $P\\le N_G(P\\cap Q)$, so $\\left|N_G(P\\cap Q)\\right|$ is a divisor of $\\left|G\\right|$ which has $\\left|P\\right|=" + p.p + "^{" + p.pow + "}$ as a proper divisor. Then it is easily verified that $\\left|N_G(P\\cap Q)\\right|$ is at least $" + np.ptr.data + "$. But then $N_G(P\\cap Q)$ is a subgroup of $G$ of index no more than $" + (n.n / np.ptr.data) + "$. Since $G$ acts transitively on the left cosets of $N_G(P\\cap Q)$ by left multiplication, we have a non-trivial map $\\phi: G\\to S_{" + (n.n / np.ptr.data) + "}$. Contradiction.</p>";
}

TechLAI = new Technique("large abelian intersection");
TechLAI.test = function(n, p, np){
    if(p.pow != 2 || n.countElements() + (Math.pow(p.p, 2) - 2) * np < n.n)
        return false;

    //we're looking for  divisors of p^a that ar larger than p^(a+1)
    var f = n.kModM(0, Math.pow(p.p, 2));
    np.ptr = f.head.prev;

    while(Math.pow(p.p, 3) < np.ptr.data)
        np.ptr = np.ptr.prev;

    np.ptr = np.ptr.next;

    return (n.n/np.ptr.data <= n.smartInject);

}
TechLAI.proof = function(n, p, np){
    var pf = "<p>Since the " + sylow("p") + " cannot intersect non-trivially for any prime $p$ such that $p^2\\nmid\\left|G\\right|$, at a minimum, we have ";

    var counter = 0;

    var ptr2 = n.primes.head.next;
    while(ptr2 != n.primes.head){
        if(ptr2.data.p != p.p && ptr2.data.pow == 1){
            pf += "$$" + ptr2.data.smallestNP() + "\\cdot(" + ptr2.data.toStringWithPower() + " - 1)=" + ptr2.data.smallestNP().np * (Math.pow(ptr2.data.p, ptr2.data.pow) - 1) + "\\mbox{ elements of order }" + ptr2.data.p + "$$\n";

            counter += ptr2.data.smallestNP().np * (Math.pow(ptr2.data.p, ptr2.data.pow) - 1);
        }
        ptr2 = ptr2.next;
    }

    pf += "</p><p>Furthermore, for the primes $p$ such that $p^2$ divides $\\left|G\\right|$, there are at least two Sylow $p$-subgroups $P$ and $Q$. While they may have non-trivial intersection, if we are looking for a lower bound on the number of elements in " + sylow(p) + " of $G$, we must get $p^m$ elements from $P$ (where $p^m$ divides $\\left|G\\right|$, but $p^{m+1}$ does not), and at least one more element from $Q$. Thus, we get at very least";

    ptr2 = n.primes.head.next;
    while(ptr2 != n.primes.head){
        if(ptr2.data.p != p.p && ptr2.data.pow > 1){
            pf += "$$" + ptr2.data.smallestNP() + "\\cdot(" + ptr2.data + " - 1)=" + ptr2.data.smallestNP().np * (ptr2.data.p - 1) + "\\mbox{ elements of order }" + ptr2.data.p + "^k$$\n";
            counter += ptr2.data.smallestNP().np * (ptr2.data.p - 1);
        }
        ptr2 = ptr2.next;
    }

    pf += "for a total of $" + counter + "$ elements.</p><p>Then the " + sylow(p) + " subgroups cannot have trivial intersection, lest there be another $" + np + "\\cdot(" + p + "^{" + p.pow + "} - 1)$ elements. So there must be two distinct " + sylow(p) + "s of $G$, $P$ and $Q$, such that $[P:P\\cap Q]&lt; " + p + "^2$. As this index must be a power of $" + p + "$, and $P\\ne Q$, the index must be $" + p + "$. That is, $\\left|P\\cap Q\\right|=" + p + "$.</p><p>Since every group of order $" + p.toStringWithPower() + "$ is abelian, $P\\cap Q\\lhd P$, so $P\\le N_G(P\\cap Q)$. Similarly, $Q\\le N_G(P\\cap Q)$, so $PQ\\subseteq N_G(P\\cap Q)$. We can therefore bound the size of the normalizer by $$\\left|N_G(P\\cap Q)\\right|\\ge\\left|PQ\\right|=\\frac{\\left|P\\right|\\cdot\\left|Q\\right|}{\\left|P\\cap Q\\right|}=" + p + "^{" + (p.pow + 1) + "}.$$ We also know that $P\\le N_G(P\\cap Q)$, so $\\left|N_G(P\\cap Q)\\right|$ is a divisor of $\\left|G\\right|$ which has $\\left|P\\right|=" + p.p + "^{" + p.pow + "}$ as a proper divisor. Then the possibilities for $\\left|N_G(P\\cap Q)\\right|$ are $$";

    var pe = Math.pow(p.p, p.pow);
    var x = new Num(n.n/pe);
    x.computeFactorList();
    var l = x.factors.copy();
    while(l.first() < p.p)
        l.popFront();

    var ptr = l.head.next;
    while(ptr != l.head){
        ptr.data = ptr.data * pe;
        ptr = ptr.next;
    }

    var c = 0;
    var ptr = l.head.next;
    while(ptr != l.head){
        if(n.n/ptr.data < n.smartInject)
            ++c;
        ptr = ptr.next;
    }

    if(c == l.size)
        pf += toList(l, false).s + "$$ All $" + c + "$ of these are excluded";
    else 
        pf += toList(l, false).s + "$$ The last $" + c + "$ are excluded,";

    pf += " since in each case the index $[G:N_G(P\\cap Q)]$ would be less than $" + n.smartInject + "$. This is a problem because if we have a subgroup $H$ of $G$ with index less than $" + n.smartInject + "$, then $G$ acts by left multiplication on the left cosets, which induces a non-trivial map from $G$ into $S_{[G:H]}$, which we know cannot exist when $[G:H] &lt;" + n.smartInject + "$.";

    if(c == l.size)
        return pf + "Thus, there can be no simple groups of order $" + n.n + "$.</p>";

    //otherwise there is one more case FIXME
    return pf + "</p><p>Now we may assume $N_G(P\\cap Q)$ is a subgroup of $G$ of order $" + l.first() + "$. Since there are exactly $" + np.ptr.data + "$ elements which do not belong to " + sylow(n.n/np.ptr.data) + ", and $N_G(P\\cap Q)$ always conjugates to a subgroup of order $" + np.ptr.data + "$, it must always conjugate to itself, and hence must be normal. Contradiction.</p>";
}

//FINISH ME, WHEN DO I NEED WHAT FOR COUNTING
TechCount = new Technique("count");
TechCount.test = function(n, p, np){
    var ptr = n.primes.head.next;
    np.count = 0;

    while(ptr != n.primes.head){
        //for this prime, count with this np
        if(ptr.data == p){
            if(p.pow > 1)
                np.count += Math.pow(p.p, p.pow);
            else
                np.count += np * (p.p - 1);
        }
        else{
            if(ptr.data.pow > 1)
                np.count += Math.pow(ptr.data.p, ptr.data.pow);
            else
                np.count += ptr.data.smallestNP().np * (ptr.data.p - 1);
        }

        ptr = ptr.next;
    }

    return (np.count >= n);
}
TechCount.proof = function(n, p, np){
    var pf = "<p>If $p$ divides $\\left|G\\right|$, but $p^2$ does not, then the Sylow $p$-subgroups of $G$ are all isomorphic to $" + zmod("p") + "$, and therefore are required to have trivial intersection. That is, if $p^2\\nmid\\left|G\\right|$, we can conclude that $G$ contains $n_p\\cdot(p-1)$ elements of order $p$. We conclude that $G$ has a minimum of";

    var ptr = n.primes.head.next;
    while(ptr != n.primes.head){
        var myp = (ptr.data == p ? p : ptr.data);
        var mynp = (ptr.data == p ? np : ptr.data.smallestNP().np);

        if(ptr.data.pow == 1){
            pf += "$$" + mynp + "\\cdot(" + myp + " - 1)=" + mynp * (myp.p - 1) + "\\mbox{ elements of order }" + myp + "$$\n";
        }
        else{
            pf += "$$" + myp.toStringWithPower() + "= " + Math.pow(myp.p, myp.pow) + "\\mbox{ non-identity elements in " + sylow(myp) + "s }$$\n";
        }

        ptr = ptr.next;

    }

    pf += "<p>This constitutes $" + np.count + "$ elements in Sylow subgroups in a group of order $" + n + "$";

    if(np.count == n.n){
        pf += ", which leaves no room for an identity element";
    }
    return pf + ".</p>";
}

TechDNorm = new Technique("double normalizer");
TechDNorm.test = function(n, p, np){
    np.ptr = n.primes.head.next;
    while(np.ptr != n.primes.head){

        //take a prime which divides n but not np
        if(np % np.ptr.data.p != 0 && np.ptr.data.p != p.p){

            var norm = new Num(n.n/np);
            norm.computeFactorList();

            return (norm.kModM(1, np.ptr.data.p).size == 1 &&
                    np.ptr.data.p != p &&
                    np.ptr.data.incompleteNPSize() == 1 &&
                    (n.n/np.ptr.data.smallestNP()) % Math.pow(p.p, p.pow) != 0);
        }

        np.ptr = np.ptr.next;
    }

    return false;

}

TechDNorm.proof = function(n, p, np){
    var exp = "";
    if(p.pow > 1)
        exp = "^{" + p.pow + "}";

    return "<p>Let $P_{" + p + "}$ be a " + sylow(p) + ". Then $N_G(P_{" + p + "})$ is a group of order $" + (n.n/np) + "$, and therefore has a " + sylow(np.ptr.data.p) + ", $P_{" + np.ptr.data.p + "}$. It is clear that $P_{" + np.ptr.data.p + "}$ is also a " + sylow(np.ptr.data.p) + " of $G$. Applying the Sylow counting technique to the group $N_G(P_{" + p + "})$, tells us that it contains exactly one " + sylow(np.ptr.data.p) + ", so $P_{" + np.ptr.data.p + "}\\lhd N_G(P_{" + p + "})$. Since every element of $P_{" + p + "}$ conjugates $P_{" + np.ptr.data.p + "}$ to itself, $P_{" + p + "}\\le N_G(P_{" + np.ptr.data.p + "})$. This means that $" + p + exp + "$ must divide the order of $N_G(P_{" + np.ptr.data.p + "})$. But we already know that $\\left|N_G(P_{" + np.ptr.data.p + "})\\right|=" + n + "/n_{" + np.ptr.data.p + "} = " + (n.n/np.ptr.data.smallestNP()) + "$, a contradiction.</p>";
}

TechSymDiv = new Technique("symmetric divisors");
TechSymDiv.test = function(n, p, np){
    np.ptr = n.primes.head.next;
    while(np.ptr != n.primes.head){
        if(np.ptr.data.p <= np && (np.ptr.data.p << 1) > np){
            np.norm = n.n/np;
            np.other = factorial(np - np.ptr.data.p) * np.ptr.data.p * (np.ptr.data.p - 1);
            return (np.other % np.norm != 0) || (np.other == np.norm);
        }

        np.ptr = np.ptr.next;
    }
    return false
}
TechSymDiv.proof = function(n, p, np){
    return "<p>We know that $G$ acts on the " + sylow(p) + "s by conjugation, and this action gives rise to a non-trivial map $\\phi: G\\to S_{n_{" + p + "}}=S_{" + np + "}$. If $G$ is to be simple, $\\phi$ must be injective, so we can identify $G$ with a subgroup of $S_{" + np + "}$. Moreover, $G$ must embed in $A_{" + np + "}$. If it does not, then since $A_{" + np + "}\\lhd S_{" + np + "}$, we would have $G\\cap A_{" + np + "}\\lhd G$, a non-trivial normal subgroup.</p><p>Let $P_{" + np.ptr.data.p + "}$ be a " + sylow(np.ptr.data.p) + " of $G$. Since $" + np.ptr.data.p + "^2\\nmid\\left|A_{" + np + "}\\right|$, $P_{" + np.ptr.data.p + "}$ is also a " + sylow(np.ptr.data.p) + " of $A_{" + np + "}$. This means that $N_G(P_{" + np.ptr.data.p + "})\\le N_{A_{" + np + "}}(P_{" + np.ptr.data.p + "})$. We will show that for divisibility reasons, this cannot be.</p><p>We can explicitly count the number of elements in $A_{" + np + "}$ of order $" + np.ptr.data.p + "$. They come precisely from $" + np.ptr.data.p + "$-cycles, of which there are $$\\binom{" + np + "}{" + np.ptr.data.p + "}\\cdot (" + np.ptr.data.p + "-1)!$$ Since each such element is in precisely one " + sylow(np.ptr.data.p) + " of $A_{" + np.ptr.data.p + "}$, and each " + sylow(np.ptr.data.p) + " has exactly $" + (np.ptr.data.p - 1) + "$ elements of order $" + np.ptr.data.p + "$, there are $\\binom{" + np + "}{" + np.ptr.data.p + "}\\cdot (" + np.ptr.data.p + "-2)!$ " + sylow(np.ptr.data.p) + "s.</p><p>From the Sylow theorems, we know that $\\left|N_{A_{" + np + "}}(P_{" + np.ptr.data.p + "})\\right|=" + (np.other >> 1) + "$. We also know that $\\left|N_G(P_{" + np.ptr.data.p + "})\\right|=" + np.norm + "$. However, $$N_G(P_{" + np.ptr.data.p + "})\\le N_{A_{" + np + "}}(P_{" + np.ptr.data.p + "}),$$ which contradicts Lagrange's theorem.</p>";
}


TechTwoOdd = new Technique("2^1*m", true);
TechTwoOdd.test = function(n){
    return n % 4 == 2;
}
TechTwoOdd.proof = function(n){
    return "<p>Let $G$ be a group of order $" + n + "$. By Cauchy's theorem, $G$ has has an element $g$ of order $2$. As $G$ acts on itself by left multiplication, we have a map $\\phi: G\\to S_{\\left|G\\right|}$. This map by definition is injective, so $\\phi(G)\\cong G$. Since $\\phi(g)$ also has order 2, it must be the product of disjoint $2$-cycles. Furthermore, only the identity $\\phi(e)$ has any fixed points under this action, because $hx=x$, for $h,x\\in G$ means that $h=e$. Thus, $\\phi(g)$ must be the product of $" + (n >> 1) + "$ $2$-cycles. Since a $2$-cycle is an odd permutation, and $\\phi(g)$ is the product of an odd number of them, $\\phi(g)$ must be an odd permutation. That is, $\\phi(G)\\not\\subseteq A_{" + n + "}$. In particular, since $A_{" + n + "}\\lhd S_{" + n + "}$, we know that $\\phi(G)\\cap A_{" + n + "}\\lhd \\phi(G)$, meaning that $\\phi(G)$, and therefore $G$, is not simple.</p>";
}

TechNormInSym = new Technique("element size from Normalizer carefully");
TechNormInSym.test = function(n, p, np){
    var norm = new Num(n.n/np.np);

    //I can only solve the positive diophantine equation for two primes
    if(!norm.primes.size > 2 || !norm.mustBeCyclic())
        return;


    //its cyclic, so there's an element of order "norm."
    //find some np we know
    np.ptr = n.primes.head.next;
    while(np.ptr != n.primes.head){
        var x = np.ptr.data.smallestNP();
        var y = n.n/x;


        var p1 = norm.primes.first().p;
        var p2 = norm.primes.last().p;
        //compute p1,p2 inverse mod the other
        var p1i = modInverse(p1,p2);
        var p2i = modInverse(p2,p1);
        
        //can i write it as a combination?
        if(p1i && p2i && np.ptr.data.np.size == 1 && y % norm.n != 0 && norm.n != x.np && x.np < norm.n){

            //now we want to write
            //x.np = p1 * a + p2 * b
            var a = x.np * p1i % p2;
            var b = x.np * p2i % p1;
            if(a == 0)
                a = p2;
            if(b == 0)
                b = p1;

            var c = a * p1 + b * p2;
            if(c != x.np)
                return true;

        }

        np.ptr = np.ptr.next;
    }

}
TechNormInSym.proof = function(n, p, np){
    var x = new Num(n.n/np.np);
    return "<p>Let $P_{" + p + "}$ be a " + sylow(p) + ", and let $P_{" + np.ptr.data.p + "}$ be a " + sylow(np.ptr.data.p) + ". The normalizer $N_G(P_{" + p + "})$ has order $" + n.n/np.np + "$, and therefore must be cyclic, so we can pick $g\\in G$ to be an element of order $" + n.n/np.np + "$. Since $" + n.n/np.np + "$ does not divide $\\left|N_G(P_{" + np.ptr.data.p + "})\\right|=" + n + "/n_{" + np.ptr.data.p + "}=" + (n/np.ptr.data.smallestNP()) + "$, the group element $g$ cannot normalize $P_{" + np.ptr.data.p + "}$, nor any other " + sylow(np.ptr.data.p) + ". Thus, if we identify $g$ with its action on the $" + np.ptr.data.smallestNP() + "$ " + sylow(np.ptr.data.p) + ", we see that we have produced an element in $S_{" + np.ptr.data.smallestNP() + "}$ of order $" + n.n/np.np + "$ which has no fixed points.</p><p>Consider the cycle structure of $g$. If we say that $g$ has $a$ $" + x.primes.first().p + "$-cycles, and $b$ $" + x.primes.last().p + "$-cycles, we would need to find a solution to the Diophantine equation $$" + x.primes.first().p + "a+" + x.primes.last().p + "b=" + np.ptr.data.smallestNP() + ",$$ with $a,b&gt;0$. It is routine to check that no such solution exists.</p>";
}

TechOne = new Technique("is it one?", true, 1);
TechOne.test = function(n){ return n == 1 }
TechOne.proof = function(n){ return "<p>The trivial group is the only group on one element, and has no proper subgroup, let alone non-trivial normal ones, so it is vacuously simple.</p>"; }

TechSporadic = new Technique("is it a sporadic group", true, 1);
//TechSporadic.test = sporadicTest;

TechSimple = new Technique("classification theorem", true);
TechSimple.test = null;

TechPrimes = new Technique("prime or prime power", true, 2);
TechPrimes.test = function(n){ return (n.isPrime() || n.isPrimePower()); }
TechPrimes.proof = function(n){ return (n.isPrime() ? pf_prime(n.n)+(n.n == 2 ? "<center><div id = \"fsg\" class = \"ui-corner-all\"><iframe width=\"420\" height=\"315\" src=\"http://www.youtube.com/embed/UTby_e4-Rhg?autoplay=1\" frameborder=\"0\" allowfullscreen></iframe><br>Finite Simple Group (of Order Two)<br><a href = \"http://www.casa.org/node/2044\">Klein Four Group</a></div></center>" : "") : pf_prime_power(n.primes.first().p, n.n)); }

TechSylow = new Technique("does n_p only have one option", true);
TechSylow.test = function(n){
    n.ptr = n.primes.head.next
        while(n.ptr != n.primes.head){
            if(n.ptr.data.np.size == 1)
                return true;
            n.ptr = n.ptr.next;
        }

    return false;
}
TechSylow.proof = function(n){ return pf_one_mod_p(n, n.ptr.data); }

TechInjectBound = new Technique("bound the injection sizes", true);
TechInjectBound.test = function(n, b){
    n.ptr = n.primes.head.next;
    while(n.ptr != n.primes.head){
        if(n.ptr.data.np.last().np < b)
            return n.ptr.data;

        n.ptr = n.ptr.next;
    }

    return false;
}
TechInjectBound.proof = function(n){
    return pf_inject(n, n.ptr.data);
}

TechNC = new Technique("proof using NC and self-normalization");
TechNC.test= function(n, p, np){
    if(p.pow != 2 || n.primes.size != 2)
        return false;

    //show they intersect trivially
    //if not, normalizer has size at least p^3
    //find smallest factor larger than p^3
    var ptr = n.factors.head.next;
    while(ptr.data < Math.pow(p.p, 3) || ptr.data % p.p != 0){
        ptr = ptr.next;
    }
    n.k = ptr.data;
    //lower bound on the size of C_G(P_1 n P_2). size-order as well as div-order
    var k = n.k / gcd(n.k, p - 1);
    while(k % p.p == 0)
        k /= p.p;
    
    n.x = new Num(k);
    n.x.computeFactorList();
    //there exists an element of this order
    var y = n.x.primes.first();

    n.ptr = n.primes.head.next;
    while(n.ptr != n.primes.head){
        n.j = n.n / n.ptr.data.smallestNP().np;
        //FIXME this was y.n, changed it to y. FIX THIS GUY
        if(n.j % (p.p * y.n) != 0 && n.ptr.data.np.size == 1)
            if(!findElementInAlt(p.p * y.n, n.ptr.data.np.first().np))
                return true;

        //check if i can find such an element
        n.ptr = n.ptr.next; 
    }

    return false;

}
TechNC.proof = function(n, p, np){
    return "<p>We first show that all " + sylow(p) + " intersect trivially. Suppose, by way of contradiction, that $P$ and $P'$ are distinct " + sylow(p) + " with non-trivial intersection $Q$. Then $\\left|Q\\right|=" + p + "$, and $Q\\lhd P$ and $Q\\lhd P'$. Thus, we can bound the size of the normalizer by $$\\left|N_G(P\\cap P')\\right|\\ge\\left|P\\cdot P'\\right|=\\frac{\\left|P\\right|\\cdot\\left|P'\\right|}{\\left|P\\cap P'\\right|}=" + p + "^3.$$ Thus, $\\left|N_G(Q)\\right|$ is at least $" + p + "^3$ and is divisible by $" + p + "$. The smallest such divisor of $" + n + "$ is $" + n.k + "$. Since $" + n + "$ is only divisible by two primes, every possible size of $N_G(Q)$ is divisible by $" + n.k + "$.</p><p>Recall that $Q\\cong\\mathbb Z/" + p.p + "\\mathbb Z$, so $\\mbox{Aut}(Q)" + (p.p == 2 ? "$ is trivial" : "\\cong\\mathbb Z/" + (p.p-1) +"\\mathbb Z$") + ". Since $N_G(Q)/C_G(Q)$ is isomorphic to a subgroup of $\\mbox{Aut}(Q)$ by the isomorphism $$g\\cdot C_G(Q)\\mapsto (x\\mapsto g^{-1}xg),$$ we deduce that $C_G(Q)$ is divisible by $" + n.k + "/" + (p.p - 1) + "=" + (n.k/(p.p-1)) + "$. In particular, if we take $x$, a generator for $Q$, and $y$, an element of order $" + n.x.primes.first().p + "$, we can see that $xy\\in C_G(Q)$ is an element of order $" + (p.p * n.x.primes.first().p) + "$ in $G$.</p><p>Now let $P_{" + n.ptr.data + "}$ denote a " + sylow(n.ptr.data.p) + ". Since $\\left|N_G(P_{" + n.ptr.data + "})\\right|=" + n.j + "$, our element $xy$ cannot normalize $P_{" + n.ptr.data + "}$. The action of $G$ by conjugation on the " + sylow(n.ptr.data) + " induces a non-trivial map $$\\phi:G\\to S_{" + n.ptr.data.np.first() +"}.$$ As before, $\\phi$ must be injective lest its kernel be a non-trivial normal subgroup of $G$. Thus, we can identify $G$ with its image under $\\phi$. Since $A_{" + n.ptr.data.np.first() + "}\\lhd S_{" + n.ptr.data.np.first() + "}$, we know that $G\\cap A_{" + n.ptr.data.np.first() + "}\\lhd G$, implying that in fact $G&lt;A_{" + n.ptr.data.np.first() + "}$. Because $N_G(P_2)$ is the subgroup that fixes a particular point, our element $xy$ of order $" + (p.p * n.x.primes.first().p) + "$ cannot have any fixed points, and must be an even permutation. We can enumerate all possible cycle structures for $xy$ to see that no such element exists.</p>";
}

TechNC2 = new Technique("proof using NC, number 2");
TechNC2.test = function(n, p, np){
    //n=420, p=7, np=15
    if(p.pow != 1)
        return false;

    var norm = n.n/np.np;
    var g = new Num(gcd(norm, p.p - 1));

    //okay, we probably killed some stuff here we know how to deal with, but this is just being safe.
    if(g.primes.size != 1)
        return false;

    //centralizer is at least this size. moreover, there is an element in the centralizer of this order
    n.cent = norm / Math.pow(g.primes.first().p, g.primes.first().pow);

    var c = new Num(n.cent);
    if(c.primes.size != 2)
        return false;

    n.ptr = n.primes.head.next;
    while(n.ptr != n.primes.head){
        n.j = n.n / n.ptr.data.smallestNP().np;
        if(n.j % n.cent != 0 && n.ptr.data.np.size == 1)
            if(!findElementInAlt(n.cent, n.ptr.data.np.first().np))
                return true;

        //check if i can find such an element
        n.ptr = n.ptr.next; 
    }

    return false;

}
TechNC2.proof = function(n, p, np){
    return "<p>Let $P$ be a " + sylow(p) + ". Recall that $\\mbox{Aut}(P)" + (p.p == 2 ? "$ is trivial" : "\\cong\\mathbb Z/" + (p.p-1) +"\\mathbb Z$") + ". Since $N_G(P)/C_G(P)$ is isomorphic to a subgroup of $\\mbox{Aut}(P)$ by the isomorphism $$g\\cdot C_G(P)\\mapsto (x\\mapsto g^{-1}xg),$$ we deduce that $C_G(P)$ is divisible by $" + n.cent + "$. In particular, if we take $x$, a generator for $P$, and $y$, an element of order $" + (n.cent/p.p) + "$, we can see that $xy\\in C_G(Q)$ is an element of order $" + n.cent + "$ in $G$.</p><p>Now let $P_{" + n.ptr.data + "}$ denote a " + sylow(n.ptr.data.p) + ". Since $\\left|N_G(P_{" + n.ptr.data + "})\\right|=" + n.j + "$, which is not divisible by $" + n.cent + "$, our element $xy$ cannot normalize $P_{" + n.ptr.data + "}$. The action of $G$ by conjugation on the " + sylow(n.ptr.data) + " induces a non-trivial map $$\\phi:G\\to S_{" + n.ptr.data.np.first() +"}.$$ As before, $\\phi$ must be injective lest its kernel be a non-trivial normal subgroup of $G$. Thus, we can identify $G$ with its image under $\\phi$. Since $A_{" + n.ptr.data.np.first() + "}\\lhd S_{" + n.ptr.data.np.first() + "}$, we know that $G\\cap A_{" + n.ptr.data.np.first() + "}\\lhd G$, implying that in fact $G&lt;A_{" + n.ptr.data.np.first() + "}$. Because $N_G(P_2)$ is the subgroup that fixes a particular point, our element $xy$ of order $" + n.cent + "$ cannot have any fixed points, and must be an even permutation. We can enumerate all possible cycle structures for $xy$ to see that no such element exists.</p>";
}

Tech720 = new Technique("720", true);
Tech720.test = function(n){ return n.n == 720; };
Tech720.proof = function(n){
    n.computeFactorList();
    var disclaimer = "<div class=\"ui-state-highlight ui-corner-all\" style=\"margin-top: 0px; margin-bottom: 20px; padding: 1em .7em; font-size: 10pt;\"><span class=\"ui-icon ui-icon-info\" style=\"float: left; margin-right: .3em;\"></span><strong>Disclaimer:</strong> This proof is not my own work. It follows closely the proof by Derek Holt, found <a href = \"http://sci.tech-archive.net/Archive/sci.math/2006-12/msg07456.html\">here</a>, with some modifications presented by Project Crazy Project, found <a href =\"http://crazyproject.wordpress.com/2010/07/22/no-simple-group-of-order-720-exists/\">here</a>.</div>";
    var intro = pf_basic(n, false) + "<p>For each prime $p$, let $\\mbox{Syl}_p(G)$ denote the set of " + sylow("p") + "s of $G$. This is to say that $n_p=\\left|\\mbox{Syl}_p(G)\\right|$.</p>";
    var n3eq16 = "<h6>Case $n_3=16$:</h6><p>Let $P_3$ be a " + sylow(3) + ". Then $N_G(P)$ is a subgroup of $G$ of order $720/16=45$. Let $P_5$ be a " + sylow(5) + " of $N_G(P_3)$. Indeed, $P_5$ is also a " + sylow(5) + " of $G$. Every group of order $45$ is abelian, so the action of $P_3$ by conjugation fixes $P_5$. That is, $P_3\\le N_G(P_5)$. This tells us that $n_5=720/\\left|N_G(P_5)\\right|$ cannot be divisible by $3$, so $n_5=16$. Thus, $N_G(P_5)$ is a group of order $45$, and we must therefore have $N_G(P_3)=N_G(P_5)$. Let $N$ denote this abelian subgroup.</p><p>Let $Q_5$ be a " + sylow(5) + " of $G$ distinct from $P_5$. If we restrict the action of $G$ on $\\mbox{Syl}_5(G)$ to $N$, and consider the stabilizer of $Q_5$, we can see that it must be $N\\cap N_G(Q_5)=N_G(P_5)\\cap N_G(Q_5)$. We will denote this subgroup by $H$. By the orbit-stabilizer theorem, the orbits of this action must have size $1$, $15$, or $45$. Clearly $\{P_5\}$ is the only orbit with one element, and there are not even $45$ " + sylow(5) + ", so there must be an orbit of order $15$. Specifically, this orbit must be $\\mbox{Syl}_5(G)\\setminus\\{P_5\\}$. Thus, $N$ acts transitively on these subgroups, and $\\left|H\\right|=3$. This is the case for all distinct " + sylow(5) + "s $P_5$ and $Q_5$.</p><p>Now pick $R_5$ another " + sylow(5) + " distinct from $P_5$ and $Q_5$. There is some $x\\in N$ for which $R_5=x^{-1}Q_5x$, since $N$ acts transitively on $\\mbox{Syl}_5(G)\\setminus\\{P_5\\}$. Pick any $y\\in H$. Then we can compute $$(x^{-1}yx)^{-1}R_5(x^{-1}yx)=R_5,$$ so $x^{-1}yx\\in N_G(R_5)$. As $x\\in N=N_G(P_5)$, and $H$ is normal in $N$ (because $N$ is abelian), it follows that $x^{-1}Hx\\le N_G(R_5)$.</p><p>But, of course, our choice of $R_5$ was arbitrary, so $$H\\le \\bigcap_{P}N_G(xPx^{-1}),$$ where the intersection runs over all " + sylow(5) + "s of $G$. It is evident that this intersection is normal in $G$, and non-trivial since it contains $H$. The only possibility would then be that the intersection is itself $G$, but this too is impossible, for then $G$ would be equal to each term: $G=N_G(xPx^{-1})$. But if $G$ is to be simple, it cannot be the normalizer of a non-trivial proper subgroup. Thus, we have a contradiction, and $n_3\\ne16$.</p>";
    var n3eq40 = "<h6>Case $n_3=40$:</h6><p>Let $P$ be a " + sylow(3) + ", and consider the action of $P$ on $\\mbox{Syl}_3(G)$ by conjugation. Clearly the action of $P$ fixes $P$, so we may restrict its action to $\\mbox{Syl}_3(G)\\setminus\\{P\\}$, a set of $39$ elements. By the orbit-stabilizer theorem, all orbits are of size $1$, $3$, or $9$, but $1$ is excluded, since no " + sylow(3) + " can stabilize any other. Since $39$ is not divisible by $9$, there must be an orbit containing exactly $3$ " + sylow(3) + "s. This tells us that $P$ has a subgroup $Q$ of order $3$ the pointwise stabilizer of this orbit). Let $N=N_G(Q)$. We can see that $N$ has more than one " + sylow(3) + ". Therefore, it has at least $4$ (because it must have $1$ modulo $3$). This means that $\\left|N\\right|$ must be either $36$ or $72$.</p><p>If $\\left|N\\right|=36$, then $N/Q$ has order $12$. Since $N$ has $4$ " + sylow(3) + ", $N/Q$ must be isomorphic to $A_4$. As $A_4$ must act trivially on $Q$, it follows that $Q\\le Z(N)$. Thus, $N$ has a normal subgroup $H$ of order $4$. Now $H$ is contained in some " + sylow(2) + " of $G$ which has order $8$. This means that $H$ is normal in a subgroup of order $8$, and so $N_G(H)$ is a group of order divisible by $8$. Clearly $N\\le N_G(H)$, since $H$ is normal in $N$, but since $\\left|N_G(H)\\right|$ is divisible by $8$, the containment is strict. Now $N_G(H)$ has order at least $72$. It cannot be any larger, lest it have index less than $7$ in $G$, so $\\left|N_G(H)\\right|=72$.</p><p>Now let $O_3(N_G(Q))$ be the intersection of all " + sylow(3) + "s of $N_G(Q)$. We can see that $Q=O_3(N_G(Q))$ and is therefore characteristic in $N_G(Q)$. Since $N_G(Q)$ has index $2$ in $N_G(H)$, and is therefore normal in $N_G(H)$, it follows that $Q\\lhd N_G(H)$. This is of course a problem, because $N_G(H)$ is not contained in $N_G(Q)$.<p>We may therefore assume that $\\left|N\\right|=72$. Recall that $N_G(Q)/C_G(Q)$ is isomorphic to a subgroup of $\\mbox{Aut}(Q)\\cong\\mathbb Z/2\\mathbb Z$ by $$g C_G(Q)\\mapsto (x\\mapsto g^{-1}xg).$$ If $c$ denotes $\\left|C_G(Q)\\right|$, we have that $72/c$ is a factor of $2$. That is, $c=72$ or $c=36$. In either case, there is an element $x$ of order $2$ which centralizes $Q$. Let $y$ be a generator for $Q$. Then $xy$ is an element of order $6$ centralizing $Q$.</p>";
    var options = "<p>Consider the action of left multiplication on the left cosets of $N_G(Q)$ in $G$ (of which there are $10$). Expressing the action of $y$ as a product of disjoint cycles, it must be either the product of $1$, $2$, or $3$ $3$-cycles. We will show that in each of these cases, we can find elements in $C_G(Q)$ whose action is given by an odd permutation in $S_{10}$. This is a problem, because, if $G$ is to be simple, because its action naturally gives us a non-trivial map into $S_{10}$, the map must be injective. Then, if we identify $G$ with its image in $S_{10}$, $G\\cap A_{10}\\lhd G$, so if $G$ is to be simple, it must embed in $A_{10}$.</p><ul><li><p>If $y$ is a single $3$-cycle, considerng conjugates of $y$ yields an immediate contradiction.</p></li><li><p>If $y$ is two $3$-cycles, then $x$ must interchange those cycles, making $xy$ a $6$-cycle. Since $xy$ is self-centralizing, an element of $C_G(Q)$ not in $\\langle xy\\rangle$ must fix all six points in the $6$-cycle. Such an element could only be a single transposition, which is an odd permutation, and therefore not possible.</p></li><li><p>If $y$ consists of three $3$-cycles, then $x$ must interchance two of them, and fix the other pointwise. That is, $x$ must consist precisely of three transpositions, which is odd, and therefore not possible.</p></li></ul>";
    var n3eq10 = "<h6>Case $n_3=10$:</h6><p>Let $P$ be a " + sylow(3) + ", and let $N=N_G(P)$. We know that $\\left|N\\right|=720/10=72$. We also know that $G$ acts transitively by conjugation on the $10$ " + sylow(3) + ", so we get a non-trivial (and hence injective) map $\\phi:G\\to S_{10}$. We can identify $G$ with $\\phi(G)$ in $S_{10}$. If we identify $P$ with $1$, in $\\{1,\\dots,10\\}$, we see that $N$ is the stabilizer of $1$ under this action.</p><p>If $P$ is cyclic, then, since $P\\le N$, a generator $x$ for $P$ must act as a $9$-cycle on $\\{2,\\dots,10\\}$. However, $\\mbox{Aut}(P)\\cong(\\mathbb Z/9\\mathbb Z)^\\times\\cong\\mathbb Z/6\\mathbb Z$ which is abelian. This means there is an element of order $2$ which centralizes $P$. In particular, there is an element $y$ of order $2$ for which $y^{-1}xy=x$. This is not possible.</p><p>It follows that $P\\cong(\\mathbb Z/3\\mathbb Z)^2$. Let $Q$ be a $3$-element subgroup of $P$, and consider the action of $Q$ by conjugation on the " + sylow(3) + " of $G$. Certainly $Q$ fixes $P$, but if $Q$ fixes more than one " + sylow(3) + ", then $N_G(Q)$ has more than one " + sylow(3) + ", yielding a contradiction as before. Thus, $P$ acts on $\\{2,\\dots,10\\}$ without any fixed points. Moreover, we can assume without loss of generality that $P=\\langle a,b\\rangle$ where $$a=(2,3,4)(5,6,7)(8,9,10)$$ $$b=(2,5,8)(3,6,9)(4,7,10).$$</p><p>Let $S$ denote the stabilizer of $2$ in the subgroup $N$ of $G$. We know $\\left|S\\right|=8$ and is therefore a " + sylow(2) + " of $N$. Now $S$ is contained in the subgroup $H$ of $N_G(N)$ which stabilizes $2$. But $S$ is contained in $N_{S_{10}}(N)$, which we can identify with $\\mbox{Aut}(P)\\cong\\mbox{GL}_2(\\mathbb F_3)$. Note that $(5,8)(6,9)(7,10)\\in N_G(N)$ is an odd permutation, and so, under this correspondence is identified with an element of determinant $-1$. Since $\\mbox{SL}_2(\\mathbb F_3)$ is the unique index $2$ subgroup of $GL_2(\\mathbb F_3)$, it follows that $SL_2(\\mathbb F_3)$ must correspond to the even permutations in $H$. Thus, $S$ corresponds to a " + sylow(2) + " of $H$, which is isomorphic to the quaternion group $\\mathbb H$. Since all such " + sylow(2) + " are conjugate, we may therefore assume that $S=\\langle c,d\\rangle$ with $$c=(3,5,4,8)(6,7,10,9)$$ $$d=(3,6,4,10)(5,9,8,7).$$ Note that $G$ is $3$-transitive, and no non-identity element fixes more than $2$ points.</p>";
    var theRest = "<p>We know $\\left|N_G(S)\\right|=16$, and therefore contains an element $e$ not in $S$ which contains a $2$-cycle containing $1$. Without loss of generality, let that $2$-cycle be $(1,2)$. The element $e$ must also normalize a $4$-element subgroup of $S$. This subgroup could be $\\langle c\\rangle$, $\\langle d\\rangle$, or $\\langle cd\\rangle$. The cases are nearly identical, so we will only show the case $\\langle c\\rangle$. We may multiply $e$ by an appropriate element of $S$ to get $e'$ which fixes the point $3$. Since $e'$ fixes at most two points, it must invert $\\langle c\\rangle$ and therefore contain the cycle $(5,8)$. This leaves two possibilities for $e'$:</p><ul><li><p>$e'=(1,2)(5,8)(6,9)(7,10)$</p></li><li><p>$e'=(1,2)(5,8)(6,7)(9,10)$</p></li></ul><p>The first of these two options is implossible, because $b\\cdot e'$ fixes $3$ points (namely $8$, $9$, and $10$). Thus, $$e'=(1,2)(5,8)(6,7)(9,10),$$ and it is clear that $G=\\langle a,b,c,d,e'\\rangle$. In fact, this group must be the Mathieu group $M_{10}$ which is known to not be simple (though we don't need this fact). We can check that $\\langle a,b,c,e'\\rangle$ is a subgroup of $G$ of order $360$. As subgroups of index $2$ are always normal, $G$ cannot be simple.</p>";
    return disclaimer + intro + n3eq16 + n3eq40 + options + n3eq10 + theRest;
}
Tech840 = new Technique("840", true);
Tech840.test = function(n){ return n.n == 840; };
Tech840.proof = function(n){
    n.computeFactorList();
    var disclaimer = "<div class=\"ui-state-highlight ui-corner-all\" style=\"margin-top: 0px; margin-bottom: 20px; padding: 1em .7em; font-size: 10pt;\"><span class=\"ui-icon ui-icon-info\" style=\"float: left; margin-right: .3em;\"></span><strong>Disclaimer:</strong> This proof is not my own work. It follows closely the proof by Guillermo Mantilla, found <a href = \"http://www.math.wisc.edu/~jensen/Algebra/ThmsGroups.pdf\">here</a>.</div>";

    var opt = new Option({n: 840}, 8);
    opt.other = 42;
    opt.norm = 105;
    var p = 7;
    opt.ptr = {data: {p: 7}};
    var n7eq8 = "<h6>Case $n_7=8$:</h6>" + TechSymDiv.proof(n, p, opt);

    var n7eq15 = "<h6>Case $n_7=15$:</h6><p>If $n_7=15$, then for a " + sylow(7) + " $P$, $\\left|N_G(P)\\right|=56$. Since $N_G(P)/C_G(P)$ is isomorphic to a subgroup of $\\mbox{Aut}(P)\\cong\\mathbb Z/6\\mathbb Z$ by the isomorphism $$g\\cdot C_G(P)\\mapsto (x\\mapsto g^{-1}xg),$$ we deduce that $C_G(P)$ is divisible by $28$. In particular, there is an element $x$ of order $2$ which centralizes $P$, and an element $y$ which generates $P$ which commute. Their product, $xy$, has order $14$. Note that $xy$ cannot normalize any other " + sylow(7) + " $Q$, because if it did, then $(xy)^2=y^2$ would normalize $Q$, but $y^2$ generates $P$, and no element of $P$ normalizes any other " + sylow(7) + ". Thus, if we identify $xy$ with its action on the " + sylow(7) + "s of $G$, we see that $xy$ must be an element of order $14$ in $A_{15}$ which fixes precisely one point (namely, $P$). We can see that this is not possible by considering its cycle structure.</p>";
    var n7eq120 = "<h6>Case $n_7=120$:</h6><p>We can account for $120\\cdot (7-1)=720$ elements of order $7$. We may also account for, a minimum of $21\\cdot(5-1)=84$ elements of order $5$, and $10\\cdot(3-1)=20$ elements of order $3$. Altogether, this constitutes $$720+84+20=824\\mbox{ elements,}$$ leaving room for only $16$ more. However, the union of $7$ " + sylow(2) + "s constitutes at least $7\\cdot 8-6\\cdot 4=32$ new elements, a contradiction.</p>";


    return disclaimer + pf_basic(n, false) + n7eq8 + n7eq15 + n7eq120;
}
Tech756 = new Technique("756", true);
Tech756.test = function(n){ return n.n == 756; };
Tech756.proof = function(n){
    n.computeFactorList();
    var disclaimer = "<div class=\"ui-state-highlight ui-corner-all\" style=\"margin-top: 0px; margin-bottom: 20px; padding: 1em .7em; font-size: 10pt;\"><span class=\"ui-icon ui-icon-info\" style=\"float: left; margin-right: .3em;\"></span><strong>Disclaimer:</strong> This proof is not my own work. It follows closely the proof by Guillermo Mantilla, found <a href = \"http://www.math.wisc.edu/~jensen/Algebra/ThmsGroups.pdf\">here</a>.</div>";
    var intro = pf_basic(n, false);

    var rest= "<p>Let $P$ and $Q$ be distinct " + sylow(3) + "s of $G$, and let $H=P\\cap Q$. Note that if $\\left|H\\right|=9$, then $H$ is normal in both $P$ and $Q$, and we can bound the size of $N_G(H)$ by $$\\left|N_G(H)\\right|\\ge\\left|P\\cdot Q\\right|=\\frac{\\left|P\\right|\\cdot\\left|Q\\right|}{\\left|H\\right|}=81.$$ This means that $[G:N_G(H)]$ is no more than $7$. Now if we let $G$ act on the left cosets of $N_G(H)$ by left multiplication, the action induces a non-trivial (injective) map from $G$ into $S_7$ which we know cannot exist.</p><p>If $\\left|H\\right|=1$ for all pairs of " + sylow(3) + "s $P$ and $Q$, then we have $28\\cdot(27-1)=728$ non-trivial elements in " + sylow(3) + "s, and $36\\cdot(7-1)=216$ elements in " + sylow(7) + "s, which is plainly a contradiction.</p><p>We may therefore assume that there exist " + sylow(3) + "s $P$ and $Q$ with intersection $H$ of order $3$. Then we can find subgroups $P'$ and $Q'$ such that $H&lt;P'&lt;P$ and $H&lt;Q'&lt;Q$. Clearly $H$ is normal in both $P'$ and $Q'$, so we can bound the size of $N$ by $$\\left|N\\right|\\ge\\left|P'\\cdot Q'\\right|=\\frac{\\left|P'\\right|\\cdot\\left|Q'\\right|}{\\left|H\\right|}=27.$$ Of course, $N$ is not a group of order $27$, because then $N$ would be a " + sylow(3) + " whose intersection with $P$ would be $P'$, a subgroup of order $9$, which we already know is impossible. Thus, the smallest divisor of $756$ larger than $27$ and divisible by $\\left|P'\\right|=9$ is $36$, so $\\left|N\\right|\\ge36$. Moreover, any larger divisor satisfying these conditions would force $N$ to have index less than $9$ in $G$, which we know cannot happen, so $N$ is a subgroup of order $36$.</p><p>Let $R$ be a " + sylow(3) + " of $N$, and consider $N_G(R)$. Certainly $R$ is normal in a " + sylow(3) + " $P_0$ of $G$ containing $R$. If $R$ were normal in $N$, then $N_G(R)$ would necessarily have order at least $$\\left|N_G(R)\\right|\\ge \\frac{\\left|P_0\\right|\\left|N\\right|}{\\left|P_0\\cap N\\right|} = 108,$$ and be a subgroup of index $7$, yielding a contradiction. Thus, $R$ is not normal in $N$, and so $N$ must have more than one " + sylow(3) + ". Since the number of such subgroups must be $1$ modulo $3$ and a divisor of $36$, we know there are exactly $4$ " + sylow(3) + "s of $N$.</p>";
    var rest2 = "<p>We now argue that $Z(N)$ is a $3$-group. Since $N$ has four " + sylow(3) + "s, there is a subgroup $N_0$ of order $3$ which is normal in $N$. Since $N/C_N(N_0)$ is isomorphic to a subgroup of $\\mbox{Aut}(N_0)\\cong\\mathbb Z/2\\mathbb Z$ by the isomorphism $$g\\cdot C_N(N_0)\\mapsto (x\\mapsto g^{-1}xg),$$ we deduce that $C_N(N_0)$ has index at most two in $N$. Recall that in any group of order 18, there is a unique " + sylow(3) + ", which is necessarily characteristic. Then, if $C_N(N_0)$ has index $2$ (order $18$), every " + sylow(3) + " of $C_N(N_0)$ would be normal in $N$, contradicting the fact that there is more than one " + sylow(3) + " in $N$. Thus, $H$ is central in $N$. This tells us that $Z(N)$ has order divisible by $3$, but not by $9$, lest there be a single " + sylow(3) + " in $N$. This means $Z(N)$ has order $3$, $6$, or $12$. Having order $12$ is not possible, because then, $N/Z(N)$ would be cyclic, implying that $N$ was abelian, which it cannot be. If $Z(N)$ were order $6$, it would have to be $\\mathbb Z/6\\mathbb Z$, and so it would have an index two subgroup which was normal in $N$. However, this contradicts the fact that $N$ can have no subgroups of index $2$. Thus, the only possibility is that $Z(N)$ has order $3$.</p><p>We then know that $Z(N)$ is contained in some " + sylow(3) + " of $N$, and hence, by conjugating, all " + sylow(3) + "s of $N$. Thus, the number of " + sylow(3) + "s in $N/Z(N)$ is equal to the number in $N$, which is $4$. Since $N/Z(N)$ has order $12$, we see that it has $8$ elements of order $3$, leaving room for exactly one " + sylow(2) + ". By the correspondence theorem, if we have two " + sylow(2) + "s  $\\tilde P$ and $\\tilde Q$ of $N$, then $\\tilde PZ(N)=\\tilde QZ(N)$. Since $\\tilde P\\lhd\\tilde PZ(N)$ and similarly for $\\tilde Q$, and $\\tilde P$ is the unique " + sylow(2) + " of $\\tilde PZ(N)$, it follows that $\\tilde P=\\tilde Q$. In other words, $N$ has a unique " + sylow(2) + ". So if $S$ is a " + sylow(2) + " of $N$ (and also of $G$), we have $N_G(S)$ has order at least $36$, since $N\\le N_G(S)$, and, for similar reasons to before, must have order exactly $36$. In other words, $N=N_G(S)$. It follows that $n_2=756/36=21$.</p>";
    var rest3 = "<p>Let $X=\\{N_1,\\dots, N_{21}\\}$ denote the set of normalizers of the $21$ "+ sylow(2) + "s of $G$, and let $H_i=Z(N_i)$. Then $N_i$ centralizes $H_i$, so $N_i\\le C_G(H_i)$. As before, $H_i$ is order $3$. We have also seen that, any subgroup of order $36$ must be maximal, so $N_i=C_G(H_i)=N_G(H_i)$. In particular, if $i\\ne j$, then $H_i\\ne H_j$, lest $N_i=N_G(H_i)=N_G(H_j)=N_j$. Thus, the set $\\{H_1,\\dots,H_{21}\\}$ is the set of $3$-groups which are intersections of " + sylow(3) + "s. Now each $H_i$ is a central $3$-group in $N_i$, and so contained each of the four " + sylow(3) + "s of $N_i$, which have order $9$. A subgroup of order $9$ is contained in a unique " + sylow(3) + " in $G$, so $H_i$ is contained in at least four " + sylow(3) + "s of $G$. Conversely, if $K$ were a " + sylow(3) + " of $G$, Then $K$ would contain a subgroup $K'$ of index $3$ (order $9$). This would force $H_i\\lhd K'$, so $K'\\le N_G(H_i)=N_i$, making $K'$ one of the " + sylow(3) + "s of $N_i$. It follows that for each $i$, $H_i$ is contained in exactly four " + sylow(3) + "s of $G$.</p><p>Let $P_1,\\dots P_{28}$ be the $28$ " + sylow(3) + "s of $G$, and let $\\hat P_i$ denote $P_i\\setminus\\{1\\}$. The claim that each $H_i$ is contained in exactly four " + sylow(3) + "s can be stated as $$\\bigcap\\hat P_i=\\varnothing,$$ for any intersection of at least $5$ such sets. Further, there are exactly $21$ subsets of $4$ elements, one for each $H_i$, such that $\\bigcap\\hat P_i$ is non-empty (where the intersection is over four such sets). Let $\\{i_1,\\dots,i_4\\}$ be indices of the $\\hat P_i$ for such an intersection. Then $\\hat P_{i_1}\\cap\\dots\\cap\\hat P_{i_4}=H_i\\setminus\\{1\\}$. In particular, $$\\displaystyle\\sum_{\\left|I\\right|=4}\\left|\\bigcap_{i\\in I}\\hat P_i\\right|=21\\cdot(3-1)=42.$$</p><p>However, we also know that the intersection of two " + sylow(3) + "s of $G$ has size $1$ or $3$ (and therefore the same for three). Thus, $$\\displaystyle\\sum_{\\left|I\\right|=k}\\left|\\bigcap_{i\\in I}\\hat P_i\\right|=\\binom{4}{k}\\cdot21\\cdot(3-1)=\\binom4k\\cdot42,$$ for $i>1$. We may now apply the inclusion-exclusion principle to see that $$\\left|\\bigcup P_i\\right|=1+\\left|\\bigcup\\hat P_i\\right|=1+28\\cdot (27-1)-\\binom42\\cdot 42+\\binom43\\cdot42-42=603.$$ This means there are $603$ elements of in " + sylow(3) + "s in $G$, leaving room for $103$ more elements, which is not enough for the $216=36\\cdot(7-1)$ non-identity elements in " + sylow(7) + "s. Contradiction.</p>";

    return disclaimer + intro + rest + rest2 + rest3;
}


