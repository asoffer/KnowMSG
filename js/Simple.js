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



