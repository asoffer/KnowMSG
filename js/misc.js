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
