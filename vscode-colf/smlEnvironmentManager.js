// copied from https://github.com/vrjuliao/sml-vscode-extension
const spawn = require("child_process").spawn;
const vscode = require("vscode");
const pathutil = require('path')
const fs = require('fs')
// const uri2path = require('file-uri-to-path');
let sml;
let diagnostics;
const smlOutput = vscode.window.createOutputChannel("CoLF");
let cid = 0; // increase per processing
let pendingLines = [];
let currentTimeOutOfProcessing = undefined;
let errorWebviewPanel;


let statusBarItem;

function resetDiagnostics(){
	pendingLines = [];
	// diagnostics.clear();
}

let processPendingLines = function (){
	currentTimeOutOfProcessing = undefined;
	cid += 1;
// COPIED FROM https://marketplace.visualstudio.com/items?itemName=freebroccolo.sml
// NOTICE: possibly without copyright as the code is not under a open source license (it is closed source! 
// I extracted the code from the vscode extension market place)
// SO I am not going to publish this (or redistribute) until the author has given explicit permission
	diagnostics.clear();
	errregex = /^(.+?):(\d+)\:(\d+)(?:-(\d+):(\d+))?:?\s?(\b(?:Error)\b):\s(.*(?:\n\s+.*)*)/m;
	const collatedDiagnostics = new Map();
	let i = 0; 
	let webviewContent = [];
	while ( i < pendingLines.length) {
		const line = pendingLines[i];
		let match = line.match(errregex)
		if (match == null){
			i++;
			continue;
		}
		match.shift();
		const path = match.shift();
		let uri;
		try {
			// uri = vscode.Uri.parse(`file://${rootPath}/${path}`);
			// uri = vscode.Uri.file(path);
			uri = path;
		}
		catch (err) {
			continue;
		}
		if (!collatedDiagnostics.has(uri))
			collatedDiagnostics.set(uri, []);
		const curdiagnostics = collatedDiagnostics.get(uri);
		const startLine = parseInt(match.shift(), 10) - 1;
		const startChar = parseInt(match.shift(), 10) - 1;
		const endLine = parseInt(match.shift(), 10) - 1 || startLine;
		const endChar = parseInt(match.shift(), 10) - 1 || startChar;
		match.shift();
		let message = match.shift();
		webviewContent.push(`${path}:${startLine + 1}:${startChar + 1}-${endLine + 1}:${endChar + 1}`);
		webviewContent.push(message);
		// collect all messages before next diagnostic line
		i++;
		while (i < pendingLines.length && pendingLines[i].match(errregex) == null){
			if (/^\[Closing file/.test(pendingLines[i]))
			{
				// filter out certain twelf statistical information
			}
			else
			{
				message += "\n" + pendingLines[i];
				webviewContent.push(pendingLines[i]);
			}
			i++;
		}
		// we've either reached the end of the output or next err line
		if (message != ""){
			const range = new vscode.Range(startLine, startChar, endLine, endChar);
			const item = new vscode.Diagnostic(range, message, vscode.DiagnosticSeverity.Error);
			curdiagnostics.push(item);
		} else {
			console.log("bug?? empty err message from colf server")
		}


	}
	// for (const [key, value] of collatedDiagnostics.entries()) {
	// 	// remove the errors count that is printed at the end of every file
	// 	if (value.length > 2){
	// 		value.pop();
	// 	}
	//   }
	let allDiags = Array.from(collatedDiagnostics.entries());
	let errsCount = 0;
	diagnostics.set(allDiags.map(([path, errs]) => {
		let uri =vscode.Uri.file(path);
		// remove the errors count that is printed at the end of every file
		if (/\d+\serrors?\sfound/.test(errs[errs.length -1].message)){
			errs.pop();
		}
		errsCount += errs.length;
		return [uri, errs];
	}));
	console.log("diag set");
	if (errsCount == 0){
		statusBarItem.text = `CoLF: OK`
	} else {
		statusBarItem.text = `CoLF: ${errsCount} error${errsCount > 1 ? "s" : ""} found`
	}
	statusBarItem.show();

	if (vscode.workspace.getConfiguration().get("show-errors-view", true) && !errorWebviewPanel) {
		createErrorWebview();
	}
	if (errorWebviewPanel) {
		console.log("updating webview");
		if (webviewContent.length === 0) {
			console.log("no errors");
			webviewContent = ["No errors", ""].concat(pendingLines);
		} else {
			console.log("errors");
			webviewContent = ["Total " + errsCount + " errors."].concat(webviewContent);
		}
		errorWebviewPanel.webview.html = getWebviewContent(webviewContent);
	}
}

const process_saved_file = (filePath) => {

	const interpreter = vscode.workspace
	.getConfiguration()
	.get("colf-server-path", "/usr/local/bin/colf");

	if (fs.existsSync(interpreter) === false) {
		vscode.window.showErrorMessage("CoLF server not found. Please set the correct path in the settings. Current Path: " + interpreter);
		return;
	}


	var cwd = {};
	if (vscode.workspace.workspaceFolders !== undefined) {
		var wd = vscode.workspace.workspaceFolders[0].uri.fsPath;
		console.log("setting path to: " + wd);
		cwd = { cwd: wd };
	} else {
		console.log("Unable to set working directory, no current workspace folder");
	}
	if (sml){
		sml.kill();
		sml = undefined;
	}

	smlOutput.appendLine("starting " + interpreter + " --v2 " + filePath);
	let localsml = spawn(interpreter, ["--v2", filePath], Object.assign({ shell: true }, cwd));
	 sml = localsml
	
	sml.stdin.setEncoding("utf-8");
	sml.stdout.setEncoding("utf-8");
	sml.stderr.setEncoding("utf-8");
	console.log("started");
	// sml.stdin.write("help\n", (e) => {
	// 	if (e){console.log("error writing", e) }
	// });

	sml.on("error", function (err) {
		console.log(err);
		smlOutput.append(err.message);
	});

	sml.stderr.on("data", (data) => {
		// smlOutput.show(false);
		smlOutput.append(data + `\n`);
		allowNextCommand = true;
	});

	sml.stdout.on("data", (data) => {
		// smlOutput.show(false);
		smlOutput.append(data + `\n`);
		pendingLines = pendingLines.concat(data.toString().split("\n"));
		if (currentTimeOutOfProcessing) {
			clearTimeout(currentTimeOutOfProcessing);
		}
		currentTimeOutOfProcessing = setTimeout(() => {
			processPendingLines();
		}, 50); // 50 ms delay before processing events, cancel processing if additional data received within 50ms
	});
	// smlOutput.show(true);
}


function createErrorWebview() {
    if (errorWebviewPanel) {
        errorWebviewPanel.reveal(vscode.ViewColumn.Beside);
        return errorWebviewPanel;
    }

    errorWebviewPanel = vscode.window.createWebviewPanel(
        'smlErrors', // Internal ID
        'CoLF Error Viewer', // Panel Title
        vscode.ViewColumn.Beside, // Show beside the active editor
        {
            enableScripts: true, // Allow JavaScript in the webview
            retainContextWhenHidden: true, // Keep context when hidden
        }
    );

    errorWebviewPanel.onDidDispose(() => {
        errorWebviewPanel = undefined;
    });

    errorWebviewPanel.webview.html = getWebviewContent([]);
    return errorWebviewPanel;
}



function getWebviewContent(errorMessages) {
    return `
        <!DOCTYPE html>
        <html lang="en">
        <head>
            <meta charset="UTF-8">
            <meta name="viewport" content="width=device-width, initial-scale=1.0">
            <style>
                body {
                    font-family: monospace;
                    white-space: pre-wrap; /* Wraps long lines */
                    color: black;
                    padding: 10px;
                    margin: 0;
                }
            </style>
        </head>
        <body>
			<h1>CoLF Errors (${errorMessages[0]})</h1>
            ${errorMessages.map(msg => `<div>${escapeHtml(msg)}</div>`).join('\n')}
			${errorMessages.length === 0 ? '<div>No errors.</div>' : ''}
        </body>
        </html>
    `;
}

// Escape HTML to prevent injection
function escapeHtml(unsafe) {
    return unsafe
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;")
        .replace(/"/g, "&quot;")
        .replace(/'/g, "&#039;");
}
function start() {
	allowNextCommand = false;

	diagnostics = vscode.languages.createDiagnosticCollection("colf");
	statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right);
	statusBarItem.name = "CoLF Status"
	// smlOutput.show(true);

	
	// to get type inference
	createErrorWebview();
	
}


function didSaveDocument(document) {
	console.log ("detected save " + document.uri);
	smlOutput.appendLine ("detected save " + document.uri);
	if ( document.languageId == "colf"){
		statusBarItem.text = `CoLF: Checking`
		let path = document.uri.fsPath;
		resetDiagnostics();
		let supposedConfigFile = pathutil.join(pathutil.dirname(path) ,  "/sources.cfg");
		let configExists = fs.existsSync(supposedConfigFile);
		if (configExists) {
			smlOutput.appendLine("path is " + supposedConfigFile);
			// sml.stdin.write("Config.read " + supposedConfigFile + "\nConfig.load\n", (e) => {
			// 	if (e){(console.log ("error writing", e))}});
			process_saved_file(supposedConfigFile);
		} else {
			smlOutput.appendLine("path is " + path);
			// sml.stdin.write("reset\nloadFile " + path + "\n", (e) => {
			// 	if (e){(console.log ("error writing", e))}});
			process_saved_file(path);
		}
		console.log("command sent")
		// sml.stdin.flush();
	} else {
		smlOutput.appendLine("ignored uri "+ document.uri);
	}
}


function restart() {
	// if (sml.exitCode !== 0 && !sml.exitCode) {
	// 	sml.stdin.end();
	// }
	// sml.kill();
	statusBarItem.dispose();
	errorWebviewPanel.dispose();
	start();
}
	
function stop() {
	// sml.stdin.end();
}

module.exports = {
	start,
	stop,
	restart,
	didSaveDocument
};
