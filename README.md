__Warning this library is outdated, it has been merged into the rascal project. See `analysis::flow::ObjectFlow` and `lang::java::flow::JavaToObjectFlow`__


This library translates a Java AST (extracted by m3) to the Object Flow Graph language.

## How to install it?
__make sure you have [installed rascal](http://www.rascal-mpl.org/start/)!__
### Command line

1. Navigate to the workspace directory your Eclipse
- Clone this project
- In Eclipse: import existing projects, point the wizard to the workspace directory
- It will find a new project `rascal-OFG`, add that

### Inside Eclipse

1. Use import project from git and point it to this repository.
2. Good luck!
3. In case Eclipse messes it up, see the command-line approach.

## How to import it?
### New project

1. Create a new rascal project
-  In the new project wizard, add a reference to the `rascal-OFG` project
-  Type `import lang::ofg::ast::Java2OFG;` in the console to see it can find the library.

### Existing project
1. Open the properties of your project
2. go to `Java Build Path`
3. Open the "tab" `projects` 
4. Click `Add...` and choose the `rascal-OFG` project

## How to use it?
The module [`lang::ofg::ast::FlowLanguage`](src/lang/ofg/ast/FlowLanguage.rsc) contains an [ADT](http://tutor.rascal-mpl.org/Rascal/Declarations/AlgebraicDataType/AlgebraicDataType.html) modeling Tonella and Potrich Object Flow Graph language.

The [`lang::ofg::ast::Java2OFG`](src/lang/ofg/ast/Java2OFG.rsc) module translates a [m3 AST](http://tutor.rascal-mpl.org/Rascal/Libraries/lang/java/m3/AST/Declaration/Declaration.html) into the OFG ADT. 

## I found a bug!

If you have found a bug, please provide a __short snippet of java code__ which shows what goes wrong. And file an issue on this github project.

_We welcome pull-requests! ;-)_
