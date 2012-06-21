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
        if(Tech720.apply(this))
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


        if(this.proofComplete){
            this.proof += pf_basic(this, this.needSmart);

            /*
               var ptr = this.primes.head.next;
               while(ptr != this.primes.head){
               this.proof += ptr.data.showProof();

               ptr = ptr.next;
               }
               */


            var ptr = this.workedOptions.head.next;
            //do all but the last one
            while(ptr != this.workedOptions.head.prev){
                //just dump everything
                var ptr2 = ptr.data.head.next;
                while(ptr2 != ptr.data.head){
                    this.proof += "<h6>Case $n_{" + ptr2.data.p +"}=" + ptr2.data.np + "$:</h6>" + ptr2.data.proof;

                    ptr2 = ptr2.next;
                }

                //FIXME now we know the following:
                this.proof += "<p>Now we know the following shit!</p>";

                ptr = ptr.next;
            }

            ptr2 = ptr.data.head.prev;
            while(ptr2 != ptr.data.head){
                //FIXME this is a dump. be careful on display
                if(this.workedOptions.size == 1 && ptr.data.size == 1){
                    this.proof += ptr2.data.proof;
                }
                else{
                    this.proof += "<h6>Case $n_{" + ptr2.data.p +"}=" + ptr2.data.np + "$:</h6>" + ptr2.data.proof;
                }

                ptr2 = ptr2.prev;
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

