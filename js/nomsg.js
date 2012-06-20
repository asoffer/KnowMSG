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
//            TechWacky.apply(this.n, this, ptr.data);

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
    },

    showProof: function(){
        var pf = "";

        //okay, for now, just dump everything and don't even worry about the order
        var ptr = this.np.head.next;
        while(ptr != this.np.head){
            pf += "<h6>Case $n_{" + this.p + "}=" + ptr.data.np + "$:</h6>" + ptr.data.proof;

            ptr = ptr.next;
        }

        return pf;
    }
};
/*/

  var pf = "";

//if we have a proof
if(this.proofComplete){

//if there is only one, don't show the cases
if(this.np.size == 1)
return this.np.first().proof;

//FIXME, lump cases together that can be
var ptr = this.np.head.next;

while(ptr != this.np.head){
pf += "<h6>Case $n_{" + this.p + "}=" + ptr.data.np + "$:</h6>" + ptr.data.proof;

ptr = ptr.next;
}

return pf;
}

else{
var str = ""
var ptr = this.np.head.next;
while(ptr != this.np.head){
if(ptr.data.proofComplete)
str += "<h6>Case $n_{" + this.p + "}=" + ptr.data.np + "$:</h6>" + ptr.data.proof;

ptr = ptr.next;
}

return str;
}

}
};
*/

function Num(n){
    this.n = n;

    this.primes = new List();

    this.factors = new List();

    if(Math.log(this.n) > 40){
        this.proofComplete = true;
        this.proofShown = true;
        $("#inner_statement").html("<p>Unfortunately the input is to big for me to handle.</p>");
        $("#proof").html("<p></p>");
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

    //list of all the options that have worked. some may be unnecessary in a final proof. FIXME later. its fine for a first version.
    this.workedOptions = new List();
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

        //$("#inner_statement").html("<p>Every group of order $" + this.n + "$ is simple.</p>");
        //$("#inner_statement").html("<p>There are no simple groups of order $" + this.n + "=" + showFactorization(this) + "$.</p>");

        //compute all the factors and build lists of potential n_p
        this.computeFactorList();
        this.buildNP();

        if(TechSylow.apply(this) || TechTwoOdd.apply(this))
            return;
        //$("#inner_statement").html("<p>There are no simple groups of order $" + this.n + "=" + showFactorization(this) + "$.</p>");

        //compute the injections
        this.computeInjections();

        if(TechInjectBound.apply(this, this.divInject) || TechInjectBound.apply(this, this.smartInject))
            return;

        //$("#inner_statement").html("<p>There are no simple groups of order $" + this.n + "=" + showFactorization(this) + "$.</p>");


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


        if(this.proofComplete){
            this.proof += pf_basic(this, this.needSmart);

            /*
               var ptr = this.primes.head.next;
               while(ptr != this.primes.head){
               this.proof += ptr.data.showProof();

               ptr = ptr.next;
               }
               */

            if(this.workedOptions.size == 1){
                this.proof += this.workedOptions.first().proof;
            }
            else{
                var ptr = this.workedOptions.head.next;
                while(ptr != this.workedOptions.head){
                    this.proof += "<h6>Case $n_{" + ptr.data.p + "}=" + ptr.data.np + "$:</h6>" + ptr.data.proof;

                    ptr = ptr.next;
                }
            }

            $("#inner_statement").html("<p>There are no simple groups of order $" + this.n + "=" + showFactorization(this) + "$.</p>");

            /*
            //if we actually have a proof
            while(!ptr.data.proofComplete)
            ptr = ptr.prev;

            while(ptr.data.np.first().np < this.smartInject)
            ptr.data.np.popFront();

            this.proof += pf_basic(this, this.needSmart) + ptr.data.showProof();
            */
        }
        else{
            $("#inner_statement").html("<p>There are no simple groups of order $" + this.n + "=" + showFactorization(this) + "$.</p>");
            this.proof = "<p>While I cannot find an elementary proof, "
                //try burnside
                if(this.primes.size == 2)
                    this.proof += "Burnside's Theorem tells us that for primes $p$ and $q$, and natural numbers $a$ and $b$, groups of order $p^a\\cdot q^b$ are solvable. The only solvable groups which are simple are the cyclic groups of prime order. Since $" + this.n + "$ is not prime, no group of order $" + this.n + "$ can be simple.";

            //try feit-thompson
                else if(this.n % 2 == 1)
                    this.proof += "the Feit-Thompson Theorem says that all groups of odd order are solvable. The only solvable groups which are simple are the cyclic groups of prime order. Since $" + this.n + "$ is not prime, no group of order $" + this.n + "$ can be simple.";

            //use the classification
                else
                    this.proof += "the classification theorem for finite simple groups tells us the possible sizes of finite simple groups, to which $" + this.n + "$ does not belong.";

            var emel = "asoffer";
            this.proof += " Below is all of the information which I could figure out in a proof-like format. Do you know an elementary technique that would solve this case? <a href = \"mailto:" + emel + "@math.ucla.edu\">Let me know</a>!</p><hr>";
            //var ptr = this.primes.head.next;

            this.proof += pf_basic(this, this.divInject != this.smartInject);

            var str = "";
            var ptr = this.workedOptions.head.next;
            while(ptr != this.workedOptions.head){
                this.proof += "<h6>Case $n_{" + ptr.data.p + "}=" + ptr.data.np + "$:</h6>" + ptr.data.proof;

                ptr = ptr.next;
            }
/*
            while(ptr != this.primes.head){
                str += ptr.data.showProof();

                ptr = ptr.next;
            }
            if(str != ""){
                //then add on the final results if anything was added on
                this.proof += str;// + "FINISH ME";
            }
*/
        }

        this.proofShown = true;
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


function sporadicTest(num){
    for(var i = 0; i < spor.length; ++i){
        if((""+num.n) == spor[i]){
            $("#inner_statement").html("<p>There exists a simple group of order $" + num +  "=" + showFactorization(num) + "$.</p>");

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
        return a % m;
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
    pf+= "$. Therefore,";

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

var GLOBAL_v = 1.3;
var GLOBAL_d = "May 10, 2012";
var GLOBAL_n = null;
var GLOBAL_fail = new Array(252,288,420,576,720,756,840);

$(function(){
    //set the version number
    $("#version").html("<span id = \"vers\">Version " + GLOBAL_v + "</span><br>Last updated "+GLOBAL_d);
    $("#vers").click(function(){
        sendMessage("Changes","<h4>What's new in Version " + GLOBAL_v + "?</h4><ul><li>Groups sizes $540, 630, 810, 990, 1890$ and more solved.</li><li>Several bugs fixed</li></ul><h4>What's new in Version 1.2?</h4><ul><li>Display issues with long lists fixed.</li><li>Potentially long lines only displayed at users choice.</li><li>Added capability to input arithmetic expressions.</li></ul>");
    });

    generateFailList();

    //set the information about NoMSG
    $("#about")
    .button({icons: {primary: "ui-icon-info"}})
    .click(function(){
        sendMessage("About NoMSG", "<h4>What is NoMSG?</h4><p>NoMSG is a proof generator. If you input a positive integer $n$, NoMSG will attempt to find a simple group of order $n$, or generate a proof that no such simple groups exist.</p><h4>How does it work?</h4><p>Magic.</p>");
    });

/*
   $("#tech")
   .button({disabled: true})
   .click(function(){
   return;
   });
   */
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
var x = 1;
var counter = new List();
while(x <= 10000){
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

        console.log(p);

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
    for(var i = 0; i < 6; ++i)
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

            n.workedOptions.pushBack(np);

            if(this.simpleType){
                var v = $("#inner_statement");
                switch(this.displayCode){
                    case 0:
                        v.html("<p>There are no simple groups of order $" + n + "$.</p>");
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
    return "<p>Since $G$ acts transitively on the " + sylow(p) + "s of $G$ by conjugation, we have a nontrivial map $\\phi:G\\to S_{" + np + "}$. If $P$ is a " + sylow(p) + " of $G$, since every element of the normalizer $N_G(P)$ fixes $P$, we in fact have a nontrivial map $\\overline\\phi=\\phi\\mid_{N_G(P)}:N_G(P)\\to S_{" + p + "}$. Since $\\left|N_G(P)\\right|=" + (p.p << 1) + "$, and the only groups of order $" + (p.p << 1) + "$ are $" + zmod(p.p << 1) + "$ and $D_{" + p + "}$, one of these must be a subgroup of $S_{" + p + "}$, which cannot be.</p>";
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
    return "<p>Since $n_{" + p + "}\\not\\equiv 1(\\bmod" + p + "^2)$, there must be two distinct " + sylow(p) + "s of $G$, $P$ and $Q$, such that $[P:P\\cap Q]&lt; p^2$. As this index must be a power of $" + p + "$, and $P\\ne Q$, the index must be $" + p + "$. That is, $\\left|P\\cap Q\\right|=" + p + np.exp + "$.</p><p>However, $P\\cap Q$ is a $" + p + "$-subgroup of $P$ with index divisible by $" + p + "$, so $" + p + "$ divides $[N_P(P\\cap Q):P\\cap Q]$, meaning $N_P(P\\cap Q)=P$. This means, $P\\cap Q\\lhd P$, so $P\\le N_G(P\\cap Q)$. Similarly, $Q\\le N_G(P\\cap Q)$, so $PQ\\subseteq N_G(P\\cap Q)$. We can therefore bound the size of the normalizer by $$\\left|N_G(P\\cap Q)\\right|\\ge\\left|PQ\\right|=\\frac{\\left|P\\right|\\cdot\\left|Q\\right|}{\\left|P\\cap Q\\right|}=" + p + "^{" + (p.pow + 1) + "}.$$ We also know that $P\\le N_G(P\\cap Q)$, so $\\left|N_G(P\\cap Q)\\right|$ is a divisor of $\\left|G\\right|$ which has $\\left|P\\right|=" + p.p + "^{" + p.pow + "}$ as a proper divisor. Then it is easily verified that $\\left|N_G(P\\cap Q)\\right|$ is at least $" + np.ptr.data + "$. But then $N_G(P\\cap Q)$ is a subgroup of $G$ of index no more than $" + (n.n / np.ptr.data) + "$. Since $G$ acts transitively on the left cosets of $N_G(P\\cap Q)$ by left multiplication, we have a nontrivial map $\\phi: G\\to S_{" + (n.n / np.ptr.data) + "}$. Contradiction.</p>";
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

    return (n.n/np.ptr.data < n.divInject);

}
TechLAI.proof = function(n, p, np){
    var pf = "<p>Since the " + sylow("p") + " cannot intersect nontrivially for any prime $p$ such that $2\\nmid\\left|G\\right|$, at a minimum, we have ";

    var counter = 0;

    var ptr2 = n.primes.head.next;
    while(ptr2 != n.primes.head){
        if(ptr2.data.p != p.p && ptr2.data.pow == 1){
            proof += "$$" + ptr2.data.smallestNP() + "\\cdot(" + ptr2.data.toStringWithPower() + " - 1)=" + ptr2.data.smallestNP().np * (Math.pow(ptr2.data.p, ptr2.data.pow) - 1) + "\\mbox{ elements of order }" + ptr2.data.p + "$$\n";

            counter += ptr2.data.smallestNP().np * (Math.pow(ptr2.data.p, ptr2.data.pow) - 1);
        }
        ptr2 = ptr2.next;
    }

    pf += "</p><p>Furthermore, for the primes $p$ such that $p^2$ divides $\\left|G\\right|$, there are at least two Sylow $p$-subgroups $P$ and $Q$. While they may have nontrivial intersection, if we are looking for a lower bound on the number of elements in Sylow $p$ subgroups of $G$, we must get $p^m$ elements from $P$ (where $p^m$ divides $\\left|G\\right|$, but $p^{m+1}$ does not), and at least one more element from $Q$. Thus, we get at very least";

    ptr2 = n.primes.head.next;
    while(ptr2 != n.primes.head){
        if(ptr2.data.p != p.p && ptr2.data.pow > 1){
            proof += "$$" + ptr2.data.smallestNP() + "\\cdot(" + ptr2.data + " - 1)=" + ptr2.data.smallestNP().np * (ptr2.data.p - 1) + "\\mbox{ elements of order }" + ptr2.data.p + "^k$$\n";
            counter += ptr2.data.smallestNP().np * (ptr2.data.p - 1);
        }
        ptr2 = ptr2.next;
    }

    return pf + "for a total of $" + counter + "$ elements.</p><p>Then the " + sylow(p) + " subgroups cannot have trivial intersection, lest there be another $" + np + "\\cdot(" + p + "^{" + p.pow + "} - 1)$ elements. So there must be two distinct " + sylow(p) + "s of $G$, $P$ and $Q$, such that $[P:P\\cap Q]&lt; p^2$. As this index must be a power of $" + p + "$, and $P\\ne Q$, the index must be $" + p + "$. That is, $\\left|P\\cap Q\\right|=" + p + "$.</p><p>Since every group of order $" + p.toStringWithPower() + "$ is abelian, $P\\cap Q\\lhd P$, so $P\\le N_G(P\\cap Q)$. Similarly, $Q\\le N_G(P\\cap Q)$, so $PQ\\subseteq N_G(P\\cap Q)$. We can therefore bound the size of the normalizer by $$\\left|N_G(P\\cap Q)\\right|\\ge\\left|PQ\\right|=\\frac{\\left|P\\right|\\cdot\\left|Q\\right|}{\\left|P\\cap Q\\right|}=" + p + "^{" + (p.pow + 1) + "}.$$ We also know that $P\\le N_G(P\\cap Q)$, so $\\left|N_G(P\\cap Q)\\right|$ is a divisor of $\\left|G\\right|$ which has $\\left|P\\right|=" + p.p + "^{" + p.pow + "}$ as a proper divisor. Then it is easily verified that $\\left|N_G(P\\cap Q)\\right|$ is at least $" + np.ptr.data + "$. But then $N_G(P\\cap Q)$ is a subgroup of $G$ of index no more than $" + (n.n/np.ptr.data) + "$. Since $G$ acts transitively on the left cosets of $N_G(P\\cap Q)$ by left multiplication, we have a nontrivial map $\\phi: G\\to S_{" + (n.n/np.ptr.data) + "}$. Contradiction.</p>";

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
    pf = "<p>We know that $G$ acts on the " + sylow(p) + "s by conjugation, and this action gives rise to a nontrivial map $\\phi: G\\to S_{n_{" + p + "}}=S_{" + np + "}$. If $G$ is to be simple, $\\phi$ must be injective, so we can identify $G$ with a subgroup of $S_{" + np + "}$. Let $P_{" + np.ptr.data.p + "}$ be a " + sylow(np.ptr.data.p) + " of $G$. Since $" + np.ptr.data.p + "^2\\nmid\\left|S_{" + np + "}\\right|$, $P_{" + np.ptr.data.p + "}$ is also a " + sylow(np.ptr.data.p) + " of $S_{" + np + "}$. This means that $N_G(P_{" + np.ptr.data.p + "})\\le N_{S_{" + np + "}}(P_{" + np.ptr.data.p + "})$. We will show that for divisibility reasons, this cannot be.</p><p>We can explicitly count the number of elements in $S_{" + np + "}$ of order $" + np.ptr.data.p + "$. They come precisely from $" + np.ptr.data.p + "$-cycles, of which there are $$\\binom{" + np + "}{" + np.ptr.data.p + "}\\cdot (" + np.ptr.data.p + "-1)!$$ Since each such element is in precisely one " + sylow(np.ptr.data.p) + " of $S_{" + np.ptr.data.p + "}$, and each " + sylow(np.ptr.data.p) + " has exactly $" + (np.ptr.data.p - 1) + "$ elements of order $" + np.ptr.data.p + "$, there are $\\binom{" + np + "}{" + np.ptr.data.p + "}\\cdot (" + np.ptr.data.p + "-2)!$ " + sylow(np.ptr.data.p) + "s.</p>"


        if(np.other % np.norm != 0){
            return pf + "<p>From the Sylow theorems, we know that $\\left|N_{S_{" + np + "}}(P_{" + np.ptr.data.p + "})\\right|=" + np.other + "$. We also know that $\\left|N_G(P_{" + np.ptr.data.p + "})\\right|=" + np.norm + "$. However, $$N_G(P_{" + np.ptr.data.p + "})\\le N_{S_{" + np + "}}(P_{" + np.ptr.data.p + "}),$$ which contradicts Lagrange's theorem.</p>";
        }

        else if(np.other == np.norm){
            return pf + "<p>From the Sylow theorems, we know that $\\left|N_{S_{" + np + "}}(P_{" + np.ptr.data.p + "})\\right|=" + np.other + "$. Moreover, we know that $G$ embeds into $A_{" + np + "}$, lest $G\\cap A_{" + np + "}\\lhd G$. So $N_{A_{" + np + "}}(P_{" + np.ptr.data.p + "}) = " + (np.other/2) + "$. We also know that $\\left|N_G(P_{" + np.ptr.data.p + "})\\right|=" + np.norm + "$. However, $$N_G(P_{" + np.ptr.data.p + "})\\le N_{A_{" + np + "}}(P_{" + np.ptr.data.p + "}),$$ which contradicts Lagrange's theorem.</p>";
        }
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
        if(p1i && p2i && np.ptr.data.np.size == 1 && y % norm.n != 0 && norm.n != x.np){

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

//------------------------------
/*
TechWacky = new Technique("wacky420");
TechWacky.test = function(n, p, np){
    np.ptr = n.primes.head.next;
    while(np.ptr != n.primes.head){
        var norm = new Num(n.n/np.np);
        norm.computeFactorList();
        if(np.np % np.ptr.data.p == 0 && np.ptr.data.p != p.p && norm.kModM(1, np.ptr.data.p).size == 1)
            return true;

        np.ptr = np.ptr.next;
    }

    return false;
}
TechWacky.proof = function(n, p, np){
    return "FIXME WACKY:" + np.np + "   " + np.ptr.data.p + "   " + p.p + " " + n.n/np.np;
}*/

TechOne = new Technique("is it one?", true, 1);
TechOne.test = function(n){ return n == 1 }
TechOne.proof = function(n){ return "<p>The trivial group is the only group on one element, and has no proper subgroup, let alone nontrivial normal ones, so it is vacuously simple.</p>"; }

TechSporadic = new Technique("is it a sporadic group", true, 1);
//TechSporadic.test = sporadicTest;

TechSimple = new Technique("classification theorem", true);
TechSimple.test = null;

TechPrimes = new Technique("prime or prime power", true, 2);
TechPrimes.test = function(n){ return (n.isPrime() || n.isPrimePower()); }
TechPrimes.proof = function(n){ return (n.isPrime() ? pf_prime(n.n) : pf_prime_power(n.primes.first().p, n.n)); }

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

