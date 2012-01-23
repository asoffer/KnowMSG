var GLOBAL_v = 1.3;
var GLOBAL_d = "Jan 22, 2012";
var GLOBAL_n = null;
var GLOBAL_fail = new Array(252,288,420,540,576,630,720);

$(function(){
    //set the version number
    $("#version").html("<span id = \"vers\">Version " + GLOBAL_v + "</span><br>Last updated "+GLOBAL_d);
    $("#vers").click(function(){
	sendMessage("Changes","<h4>What's new in Version " + GLOBAL_v + "?</h4><ul><li>Technique list added</li><li>Groups sizes _______ solved.</li><li>Simple group listing bug fixed.</li></ul><h4>What's new in Version 1.2?</h4><ul><li>Display issues with long lists fixed.</li><li>Potentially long lines only displayed at users choice.</li><li>Added capability to input arithmetic expressions.</li></ul>");
    });

    generateFailList();


    //set the information about NoMSG
    $("#about")
	.button({icons: {primary: "ui-icon-info"}})
	.click(function(){
	    sendMessage("About NoMSG", "<h4>What is NoMSG?</h4><p>NoMSG is a proof generator. If you input a positive integer $n$, NoMSG will attempt to find a simple group of order $n$, or generate a proof that no such simple groups exist.</p><h4>How does it work?</h4><p>Magic.</p>");
	});

    $("#tech")
	.button({disabled: true})
	.click(function(){
	    return;
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

		$("#proof").html("<div class=\"ui-widget\"><div class=\"ui-state-error ui-corner-all\"><span class=\"ui-icon ui-icon-alert\" style=\"float: left; margin-right: .3em;\"></span><strong>Error: </strong>Your input was not a positive integer. Please try again, with number that has a more \"positive integer\" vibe to it.</div></div>");

		MathJax.Hub.Typeset();

		return;
	    }

	    solve(x);
	    setListExpandDisplay();
	});
    
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
			 
/*    var x = 5;
    var counter = 0;
    while(x <= 500000){
	x+=6
	GLOBAL_n = new Num(x);
	GLOBAL_n.prove();
	if(!GLOBAL_n.proofComplete){
	    console.log(GLOBAL_n.n);
	    counter++;
	}
    }

    console.log("-------");
    console.log(counter);*/
			 
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
