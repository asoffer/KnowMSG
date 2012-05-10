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
