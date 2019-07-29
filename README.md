## Artefact Description  ##

### Pre-processing ###

This Python program has been firstly written by **Lincoln Smith**, and kindly given to Tianshu Wang for the use of a Honor project. 

Tianshu Wang is responsible for the function `buildAModel` and some other assitant functions. Lincoln wrote the scraper program.

Many thanks to Lincoln for his great help and contribution in this project.

The goal in this program is converting from obtained P&C data to MiniZinc model components (for many programs). 


### Constraint Model ###

We built our model in `MiniZinc`, a standard language for `Constraint Programming`.

*.mzn.
This type of files could be used to produce course schedule (selecting OSICBC solver when testing it). 

*.dzn.
This type of files are data files in MiniZinc. 


### Website Construction ###

This web-based system is under Flask - a microframe server.

Based on the rules in Flask, we store .css and images file in `static` folder, and the main page tree.html(includes javascript code) is in `templates`.


## Usage ##

Under Windows environment, after going into the target folder, write `command`:
```
set FLASK_APP=index.py
flask run
```
Under Linux, write this for the same purpose as above:
```
export FLASK_APP=index.py
flask run
```

The result from the above operation should be like this:
``` Serving Flask app "index.py"
 Environment: production
 WARNING: Do not use the development server in a production environment.
 Use a production WSGI server instead.
 Debug mode: off
 Running on http://127.0.0.1:5000/ (Press CTRL+C to quit)
```
When using our system, click `Let's Plan` when you finish the first input of course preference.

After generating a plan, to refine it, you should click on the undesired courses in the plan and after that click on `Update`.

However, anytime during using the system, resetting preference for courses is allowed.

## Environment Requirement ##

We developed and tested this artefact with `Python 3.5.5`, `BeautifulSoup 4.6.0`, `Flask 1.0.2`, `MiniZinc 2.2.3` under Windows10.

We recommend testing with the same or higher version of software or libraries that have been applied.
    
