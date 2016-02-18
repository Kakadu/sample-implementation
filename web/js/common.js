var script = null;

function registerScript (text) {
  "use strict";

  if (!script) script = document.createElement("script");
  else document.body.removeChild (script);

  script.innerHTML = text;
  document.body.appendChild(script);
}

function do_run () {
  var result = window.run ("1", "wizard");
  registerScript (result[1]);
  window [result[0]] (); 
}

function show_results (root, tree, descr) {
  clear_run_msg ();
  document.getElementById ("output").innerHTML = tree;  
  convertTree (document.getElementById (root), false);  
  pdfViewerObject = document.getElementById ("description");
  pdfViewerObject.setAttribute ("data", descr);  
  pdfViewerObject.outerHTML = pdfViewerObject.outerHTML.replace(/data="(.+?)"/, 'data="pdf/' + descr + '"');
}

function disable_actions () {
  document.getElementById ("run_button").disabled = true;
  document.getElementById ("export_button").disabled = true;
  document.getElementById ("parsed").innerHTML = "&nbsp;";
  document.getElementById ("wizard").innerHTML = "&nbsp;";
  document.getElementById ("output").innerHTML = "&nbsp;";      
}

function enable_actions () {
  document.getElementById ("run_button").disabled = false;
  document.getElementById ("export_button").disabled = false;   
}

function parser_msg (text) {
  document.getElementById ("parsemsg").innerHTML = text;
}

function run_msg (text) {
  document.getElementById ("runmsg").innerHTML = text;
}

function clear_parser_msg () {
  document.getElementById ("parsemsg").innerHTML = "&nbsp;";
}

function clear_run_msg () {
  document.getElementById ("runmsg").innerHTML = "&nbsp;";
}

function do_parse () {
   document.getElementById ("parsed").innerHTML = "&nbsp;";
   document.getElementById ("wizard").innerHTML = "&nbsp;";
   document.getElementById ("output").innerHTML = "&nbsp;";     

   clear_parser_msg ();
   clear_run_msg ();
   var textWrapper = document.getElementById("text");
   var textForParsing = textWrapper.textContent || textWrapper.innerText;
   var result = window.parse (textForParsing.replace(/\u00a0/g, " "));
   if (result[0] == "1") {
      enable_actions ();
      document.getElementById ("parsed").innerHTML = result[1];
      convertTrees ();
      expandTree ("ast");
      do_highlighting (0, 0, 0, 0);
   } else {
      disable_actions ();
      parser_msg (result[1]);
      document.getElementById ("text").innerHTML = result[2];
   }
}

function do_highlighting (x, y, z, t) {
   document.getElementById ("text").innerHTML = window.highlight (x, y, z, t);
   event.cancelBubble = true;
}

function handleFile (evt) {
  var files = evt.target.files; 
     
  if (window.File && window.FileReader && window.FileList && window.Blob) {
    var fr = new FileReader ();

    for (var i = 0, f; f = files[i]; i++) {
      fr.onload = function (e) {
        document.getElementById("text").innerHTML = "<pre class=\"inline\">" + e.target.result + "</pre>";
        disable_actions ();
      };

      fr.readAsText (f);
    }                     
  } 
  else alert('The File APIs are not fully supported by your browser.');
}

function convert () {
  var blob = new Blob([window.vertical ? window.vertical () : ""], {type: 'text/plain'});

  window.URL = window.URL || window.webkitURL;

  var href = window.URL.createObjectURL(blob);

  document.getElementById ("save").href = href;
  document.getElementById ("save").textContent = "Download";
  document.getElementById ("save").download = "vertical.t";
}

document.getElementById ("loadFile").addEventListener("change", handleFile, false);
