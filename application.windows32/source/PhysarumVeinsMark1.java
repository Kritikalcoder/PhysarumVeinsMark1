import processing.core.*; 
import processing.data.*; 
import processing.event.*; 
import processing.opengl.*; 

import java.util.ArrayList; 
import java.util.Random; 
import java.util.*; 
import processing.sound.*; 
import processing.video.*; 

import java.util.HashMap; 
import java.util.ArrayList; 
import java.io.File; 
import java.io.BufferedReader; 
import java.io.PrintWriter; 
import java.io.InputStream; 
import java.io.OutputStream; 
import java.io.IOException; 

public class PhysarumVeinsMark1 extends PApplet {







int popsize = 10000; // initial particle population size
int pixienum = popsize; // the current number of agent particles
double so = 15; // sensor offset distance (a scaling parameter)

double sa = 30; // sensor angle in degrees from forward position

double ra = 20; // rotation angle in degrees (how much the particle should turn)

boolean osc = false; // is oscillatory (flux resistant) movement activated?     *****  this would not be relevant for CA implementation
double pcd = 0; // probability of a random change in direction
double oscresetprob = 0.01f; // probability of resetting oscillation counter (if in oscillatory mode)
double depT = 5; // amount of chemoattractant trail deposited per successful step forwards
double speed = 2; // how far the particle moves each step


boolean adaptive_population_size = false; // change to true to experiment with the growth/shrinkage of populations using the parameters below

boolean do_random_death_test = true;
int division_frequency_test = 5; // how frequently to test for division
int death_frequency_test = 5; // how frequently to test for death due to overcrowding
double division_probability = 1; // probability of division (just keep it set to 1)
double death_random_probability = 0; // random death probability (just keep it set to 0)

int gw = 9; // growth window size
int gmin = 0; // growth min number of particles
int gmax = 10; // growth max number of particles
int sw = 5; // shrinkage window size
int smin = 0; // shrinkage min number of particles to survive
int smax = 24; // shrinkage max number of particles to survive
int divisionborder = 5; // do not assess for particle division if the particle is within 5 pixels range of lattice border

int startx = 15; // not used in this instance - the particles are initialised at random positions
int starty = 120;
int startradius = 5;

int linecount = 0;
boolean fileloaded = false;
String[] data; // used to parse each line of text
float[] nodex; // store node x positions
float[] nodey; // store node y positions
boolean scalenodepositions = false;
double scalevalue = 1;

boolean wrap = true; // boundary condition -- CHECK!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
double diffdamp = 0.1f; // diffusion damping value. Damping is 1-diffdamp so if diffdamp is 0.1 then the diffused value would be (value)*0.9
double projectvalue = 200; // how big is the value for the data nodes which we project onto the chemoattractant field
double suppressvalue = 2.5f; // projection value if blob is covered by particles
int suppresswindow = 3;
boolean projectnutrients = true; // project nutrients to the chemoattractant field?
int startprojecttime = 0;
int numnodes = 0; // number of nutrient 'food' node sources
int suppressradius = 5;
boolean running = false;

int wid = 400; // width of environment
int hei = 400; // height of environment
int startcol = 173; // colour agent particles can be initialised on
int wallcol = 51; // colour to represent an obstacle
int projectcol = 255; // colour to represent a nutrient site
int maxskip = 20; // how many frames to skip
boolean skipframes = false; // skip drawing some frames to increase speed?

boolean showFrameRate = true;
boolean toggleDisplayValues = true; // draw the display to include basic parameter settings (t to toggle)
boolean drawParticles = false; // are we drawing the particles or just their trail (press p to toggle)
boolean manualscaledrawtrails = true; // use a manual scaling value for trail colour?
double manualdrawscalevalue = 20; // if manual is used, this is to scale the brightness

String imagestring = "blank_400x400_gray.png"; // image for a blank circular arena

String filename = "nodedata_small-test.txt"; // node data positions in a text file
boolean useLoadedImage = true; // do we use a loaded image to represent the environment?
boolean useLoadedImageForDataProjection = false; // do we use a loaded image to store nutrient sites?
boolean useLoadedData = false; // do we load nutrient data from a text file?

int[] datax;
int[] datay;
int numdatavals = 100;

ArrayList shuffledpix;
boolean shuffle_pixie_order = true;
int nodewid = 2;
int itercount = 0;
Point pos;
PImage configImage; // loaded configuration image
PImage bgimage; // created configuration image
boolean imageloaded = false;
final double toradiansconst = 3.14159f/180;
final double todegreesconst = 180/3.14159f;
final double deg180 = 3.14159265358979f;
final double deg360 = 6.28318531f;
int maxx = wid; // boundaries of environment
int maxy = hei;
int maxxminus = wid - 1;
int maxyminus = hei - 1;
double outsidebordervalue = -1;
double[][] trail; // stores particle trail values
double[][] temptrail; // temporary trail storage for diffusion
int[][] particle_ids; // stores particle ids
int[][] griddata; // stores image / stimuli data
int[] tempids = new int[9]; // holds array of local neighbouring particle id s
ArrayList particles = new ArrayList(); // holds particle population // ISSUE!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
Particle2d tmp = new Particle2d(); // temporarily stores one particle
Grid grid; // structure to hold particle positions and chemoattractant values and to return values to sensors, and to diffuse chemoattractant
Random r = new Random();
double[] sinlut; // lookup tables for pre-computation of sin and cos
double[] coslut;
double SINCOS_PRECISION = 1;
int SINCOS_LENGTH = 361;
boolean useangleluts = true;
boolean scaletrails = true; // dynamically rescale drawing of trail values?
boolean mousestimdata = true; // do we use the mouse to project to data or to trail?
float changevalue = 2.5f; // how much do we change angles by when the user presses change keys
int stimvalue = 255; // how big is the value by which mouse stimulation is given?
String frametitle = "";
PImage pixelimage; // stores offscreen buffer of main image

PImage imagery;

WhiteNoise noise;
Capture cam;
public void setup() {


    generateAngleLUTs(); // generate look-up table for faster angle calculations
    createEnvironment();
    popsize = pixienum;
    // general initialisation    
    
    println("wid: " + wid + "  hei: " + hei);
    frameRate(25);

    grid = new Grid(wid, hei); // create the grid data structure to hold agent particles, landscape data and trails
    pixelimage = createImage(wid, hei, RGB); // create offscreen buffer
    if (imageloaded)
        grid.setAllCellData(configImage);
    if (!useLoadedImage)
        createEnvironmentConfiguration(); // if we aren't using a loaded environment then create one manually
    // initialise particles
    for (int f = 0; f < popsize; f++) {
        particles.add(f, new Particle2d(f));
        tmp = (Particle2d) particles.get(f);
        tmp.initialiseParticle();
    }
    if (shuffle_pixie_order) // randomly shuffle order of agents
        shufflePixieOrder();
    frametitle = frame.getTitle();
    running = true;

    imagery = loadImage("blank_400x400.png");

    noise = new WhiteNoise(this);
    noise.play();
    noise.amp(0.01f);

    String[] cameras = Capture.list();

    if (cameras.length == 0) {
        println("There are no cameras available for capture.");
        exit();
    } else {
        println("Available cameras:");
        for (int i = 0; i < cameras.length; i++) {
            println(cameras[i]);
        }

        // The camera can be initialized directly using an 
        // element from the array returned by list():
        cam = new Capture(this, cameras[0]);
        cam.start();
    }

}


int xx, yy;


public void draw() {
    //Map mouseY from 0 to 1

    noCursor();
    if (!running)
        return;



    scale(2); //Scales Window size in comparison to setup size



    itercount++;
    if (projectnutrients && itercount > startprojecttime)
        projectToTrail(); // project fixed data node positions as chemoattractant stimuli
    updatePopulation(); // update population (sensory and motor behaviour)
    updateTrails(); // diffuse chemoattractant trails    

    if (do_random_death_test && death_random_probability > 0 && itercount > startprojecttime)
        doRandomDeathTest(); // generallised check for random death, nowt to do with overcrowding

    if (adaptive_population_size && itercount % division_frequency_test == 0) {
        doDivisionTest();
    }
    if (adaptive_population_size && itercount % death_frequency_test == 0 && pixienum > 1) {
        doDeathTest();
    }
    if (skipframes) // if we are skipping some frames
    {
        if (itercount % maxskip != 0) {
            return;
        }
    }
    if (useLoadedImage && imageloaded) {
        image(configImage, 0, 0);
    } else {
        background(0); // clear background        
        image(bgimage, 0, 0);
    }
    if (drawParticles) // draw the particles, if necessary
    {
        drawNodePositions();
        drawParticles();
    } else {
        if (cam.available()) {
            cam.read();
            cam.loadPixels();
            float maxBri = 0;
            int theBrightPixel = 0;
            for (int i = 0; i < cam.pixels.length; i++) {
                if (brightness(cam.pixels[i]) > maxBri) {
                    maxBri = brightness(cam.pixels[i]);
                    theBrightPixel = i;
                }
            }
            xx = theBrightPixel % cam.width;
            yy = theBrightPixel / cam.width;
        }
        if (mousestimdata) {
            grid.setGridCellValue(xx / 2, yy / 2, stimvalue);
        } else {
            grid.increaseTrail(xx / 2, yy / 2, stimvalue);
        }

        drawTrailsFaster(); // draw the trails onto the screen - faster method      
    }

    if (keyPressed && key == 'x')
        outputParams();
    if (showFrameRate)
        frame.setTitle(PApplet.parseInt(frameRate) + " fps");

    noise.pan(map(mouseX, 0, width, -1.0f, 1.0f));
    noise.amp(map(mouseX + mouseY, 0, width + height, 0, 0.05f));
    //saveFrame("screen-####.jpg");
}



public void createEnvironment() {
    if (useLoadedImage) {
        loadEnvironmentImage();
    }
    if (useLoadedData) {
        readTextFile();
        startx = (int) nodex[0];
        starty = (int) nodey[0];
    }
    if (!useLoadedData && numnodes > 0)
        createNodes();
}


// test the entire population for division  
public void doDivisionTest() {
    Collections.shuffle(shuffledpix);
    Enumeration e = Collections.enumeration(shuffledpix);
    while (e.hasMoreElements()) {
        String s = (e.nextElement().toString());
        int i = Integer.parseInt(s);
        tmp = (Particle2d) particles.get(i);
        if (tmp.divide) // has this particle been tagged with the divide flag?
        {
            birthNewPixie(tmp);
        }
        tmp.divide = false;
    }
    shufflePixieOrder();
}


// create a new particle
public void birthNewPixie(Particle2d tmp) {
    // don't create any new particles if agents are on periphery
    if (tmp.curx <= 1 || tmp.curx >= maxxminus)
        return;
    if (tmp.cury <= 1 || tmp.cury >= maxyminus)
        return;
    int count = 0;
    int ind = 0;
    int freeind = 0;
    Point p = null;
    count = 0;
    ind = (int) random(9); // choose a starting cell in the nbrhood at random
    freeind = -1;
    tempids = grid.getNeighbourhoodParticleIDs(tmp.curx, tmp.cury); // get a list of spaces around current cell
    do {
        if (tempids[ind] == -1) // is this cell unoccupied (-1)?
        {
            freeind = ind; // we will birth a new agent into this one then
            break;
        } else {
            count++; // if not, keep checking all other nbrs
            ind++;
            if (ind >= 9) // if we have gone past end of list start at zero (because we started in a random position in the list of nbrs)
                ind = 0;
        }
    }
    while (count < 9); // only go thru entire list of nbrs once
    if (freeind == -1) // if there are no free nbrs then just return
        return;
    // get location of nbr and do one final check just to make sure it is empty
    p = grid.getGridLocation(freeind, tmp.curx, tmp.cury);
    if (p.x == -1 && p.y == -1) {
        println("birthnewpixie:  'free' cell is already occupied");
        return;
    }
    if (grid.getGridCellValue(p.x, p.y) == wallcol)
        return; // can't create a particle here, it is a wall
    pixienum++;
    int f = pixienum - 1;
    Particle2d birthpixie = new Particle2d(f);
    particles.add(f, birthpixie);
    //println("p now: "+pixienum+", after creating particle: "+birthpixie.id);
    birthpixie.initialiseParticle(p.x, p.y);
}



// overcrowding death test for the entire population
public void doDeathTest() {
    Iterator i = particles.iterator();
    while (i.hasNext()) {
        tmp = (Particle2d) i.next();
        if (tmp.die) // has this particle been tagged with the 'die' flag?
        {
            grid.clearGridCell(tmp.curx, tmp.cury);
            //      System.out.println("p: "+pixienum+",  killing particle: "+tmp.id);
            i.remove();
            pixienum--;
        }
    }
    shufflePixieOrder();
}


// output a range of parameters on the display screen top left corner
public void outputParams() {
    textSize(10);
    text("T: " + itercount, 2, 15);
    text("start p: " + popsize, 2, 30);
    text("curr p:" + pixienum, 2, 45);
    text("SA: " + nf((float) sa, 3, 1), 2, 60);
    //text("SA: "+ (int)sa, 2, 45);            
    text("RA: " + nf((float) ra, 3, 1), 2, 75);
    //text("RA: "+ (int)ra, 2, 55);            
    text("SO: " + (int) so, 2, 90);
    text("Osc: " + Boolean.valueOf(osc), 2, 105);
    //text("Step size: "+ (int)speed, 2, 120);      
}




public void createNodes() {
    if (useLoadedData) {
        // if we loaded the data from a text file then do nothing   
    } else // otherwise generate some points 
    {
        int borderdist = 40;
        int minsepdist = 20;
        int halfx = wid / 2;
        int halfy = hei / 2;
        int maxorigindist = halfx - borderdist;
        int countassigned = 0;
        boolean valid = true;
        Point p;
        nodex = new float[numnodes];
        nodey = new float[numnodes];
        for (int f = 0; f < numnodes; f++) {
            do {
                valid = true;
                //p = Misc.getXandYPositionWhenSuppliedWithPolarPositionAngleAndRadius(originx,originy, Misc.getDoubleRand(Misc.getRadians(360)),Misc.getDoubleRand(random_stimuli_dist_from_origin),imgwid,imghei);
                p = new Point((int) random(wid), (int) random(hei));
                if (dist(halfx, halfy, p.x, p.y) > maxorigindist)
                    valid = false;
                for (int cp = 0; cp < f; cp++) {
                    if (countassigned == 0) {
                        break;
                    }
                    if (dist(p.x, p.y, nodex[cp], nodey[cp]) < minsepdist) {
                        valid = false;
                    }
                }
            }
            while (!valid);
            nodex[f] = p.x;
            nodey[f] = p.y;
            println("Created node: " + f + " at  x: " + nodex[f] + "  ,   y: " + nodey[f]);
            countassigned++;
        }
    }
}


// shuffle the 'pack' of agents, to ensure random update order
public void shufflePixieOrder() {
    shuffledpix = null;
    shuffledpix = new ArrayList();
    for (int f = 0; f < pixienum; f++)
        shuffledpix.add(f, new Integer(f));
}



// test to reduce population by a fixed random probability per agent
// this method gradually reduces the population size if used, without using the individual particle division/death methods
// it is a global way of reducing the population size
public void doRandomDeathTest() {
    if (pixienum < 2)
        return;
    Iterator i = particles.iterator();
    while (i.hasNext()) {
        tmp = (Particle2d) i.next();
        if (tmp.r.nextDouble() < death_random_probability) {
            grid.clearGridCell(tmp.curx, tmp.cury);
            i.remove();
            pixienum--;
        }
    }
    shufflePixieOrder();
}




// convert degrees to radians
public final double getRadians(double degrees) {
    return degrees * toradiansconst;
}


// use this if projecting data nodes to trail
public void projectToTrail() {
    grid.projectToTrail();
}




// update the entire population by doing each agent's motor then sensory behaviour
public void updatePopulation() {
    if (shuffle_pixie_order) {
        Collections.shuffle(shuffledpix); // shuffle to ensure random update order
        Enumeration e = Collections.enumeration(shuffledpix);
        while (e.hasMoreElements()) {
            String s = (e.nextElement().toString());
            int i = Integer.parseInt(s);
            tmp = (Particle2d) particles.get(i);



            tmp.doMotorBehaviours();


        }
        Collections.shuffle(shuffledpix); // shuffle to ensure random update order
        e = Collections.enumeration(shuffledpix);
        while (e.hasMoreElements()) {
            String s = (e.nextElement().toString());
            int i = Integer.parseInt(s);
            tmp = (Particle2d) particles.get(i);


            tmp.doSensoryBehaviours();


        }
    }
}



// do trail chemoattractant diffusion method
public void updateTrails() {
    //grid.diffuseTrails();
    grid.diffuseTrailsFast();
}



// draw trails on the screen, rescaling them so the maximum trail value is the brightest
//
//  a very slow method....
//
public void drawTrails() {
    double scale = 0;
    if (manualscaledrawtrails)
        scale = manualdrawscalevalue;
    else {
        double max = grid.getMaxTrailValue(); // get the maxium value    
        if (max > 255) max = 255; // clip if over 255
        scale = 255 / max; // use the maximum value as the brightest
    }

    double sv = 0;
    int s = 0;
    for (int x = 0; x < wid; x++) // draw each point onto environment, must be a way to blit it across but have not done it yet - this is so slow
    {
        for (int y = 0; y < hei; y++) {
            if (griddata[x][y] == wallcol)
                continue;
            sv = scale * grid.getTrailValue(x, y);
            if (sv < 2)
                continue;
            s = (int) sv;
            if (s < 0) s = 0;
            if (s > 255) s = 255;
            stroke(s);
            point(x, y);
        }
    }
}



//
// draw trails on the screen using a faster method
//
public void drawTrailsFaster() {
    double scale = 0;
    if (manualscaledrawtrails)
        scale = manualdrawscalevalue; // are we using a manually scaled drawing value?
    else {
        double max = grid.getMaxTrailValue(); // get the maxium value    
        if (max > 255) max = 255; // clip if over 255
        scale = 255 / max; // use the maximum value as the brightest
    }
    double sv = 0;
    int s = 0;
    pixelimage.loadPixels();
    if (useLoadedImage && imageloaded) {
        pixelimage.copy(configImage, 0, 0, wid, hei, 0, 0, wid, hei); // draw the configuration image first
    }
    int count = -1;

    for (int y = 0; y < hei; y++) // draw each point onto environment, must be a way to blit it across but have not done it yet - this is so slow
    {
        for (int x = 0; x < wid; x++) {
            count++;

            pixelimage.pixels[count] = color(0, 0, 60);

        }
    }

    count = -1;

    for (int y = 0; y < hei; y++) // draw each point onto environment, must be a way to blit it across but have not done it yet - this is so slow
    {
        for (int x = 0; x < wid; x++) {
            count++;
            sv = scale * grid.getTrailValue(x, y);
            if (sv == 0) {
                continue;
            }
            s = (int) sv;
            if (s < 0) s = 0;
            if (s > 255) s = 255;

            if (s != 10)
                pixelimage.pixels[count] = color(s, 0, 60);

        }
    }
    pixelimage.updatePixels();
    image(pixelimage, 0, 0); // finally draw the image onto the screen
}


//
// draw all the particles in their positions 
//
public void drawParticles() {
    stroke(160, 4, 41); // colour of particle
    pos = new Point();
    for (int f = 0; f < pixienum; f++) {
        tmp = (Particle2d) particles.get(f);
        pos = tmp.getPosition(); // return the position of a particle
        point(pos.x, pos.y);
    }
}



// respond to interactive key presses
public void keyPressed() {
    if (keyCode == ENTER) {
        saveFrame("screen-####.jpg");
    }

    if (key == '1') // decrease SO
    {
        so--;
        if (so < 1)
            so = 1;
        displayText("SO:" + (int) so);
    } else if (key == '2') // increase so
    {
        so++;
        if (so > 40)
            so = 40;
        displayText("SO:" + (int) so);
    }
    if (key == '3') // decrease SA
    {
        sa -= changevalue;
        if (sa < 0)
            sa = 0;
        displayText("SA: " + (int) sa);
    } else if (key == '4') // increase SA
    {
        sa += changevalue;
        if (sa > 360)
            sa = 360;
        displayText("SA: " + (int) sa);
    }

    if (key == '5') // decrease RA
    {
        ra -= changevalue;
        if (ra < 0)
            ra = 0;
        displayText("RA: " + (int) ra);
    } else if (key == '6') // increase RA
    {
        ra += changevalue;
        if (ra > 360)
            ra = 360;
        displayText("RA: " + (int) ra);
    }

    if (key == '7') // decrease prob of osc reset
    {
        oscresetprob -= 0.01f;
        if (oscresetprob < 0)
            oscresetprob = 0;
        displayText("pOscReset: " + oscresetprob);
    } else if (key == '8') // increase prob of osc reset
    {
        oscresetprob += 0.01f;
        if (oscresetprob > 1)
            oscresetprob = 1;
        displayText("pOscReset: " + oscresetprob);
    }

    if (key == '9') // decrease prob of change direction
    {
        pcd -= 0.01f;
        if (pcd < 0)
            pcd = 0;
        displayText("pChangeDir: " + pcd);
    } else if (key == '0') // increase prob of change direction
    {
        pcd += 0.01f;
        if (pcd > 1)
            pcd = 1;
        displayText("pChangeDir: " + pcd);
    } else if (key == 'o') {
        osc = !osc;
        displayText("Osc: " + String.valueOf(osc));
    } else if (key == 'w') {
        wrap = !wrap;
        displayText("Wrap boundary: " + String.valueOf(wrap));
    } else if (key == 's') {
        skipframes = !skipframes;
        displayText("Skip every: " + maxskip + " frames: " + String.valueOf(skipframes));
    } else if (key == 't') {
        toggleDisplayValues = !toggleDisplayValues;
        displayText("Toggle display values:" + String.valueOf(toggleDisplayValues));
    } else if (key == 'p') {
        drawParticles = !drawParticles;
        displayText("Draw Agent Particles:" + String.valueOf(drawParticles));
    } else if (key == 'f') {
        showFrameRate = !showFrameRate;
        displayText("Display Framerate:" + String.valueOf(showFrameRate));
        // if (!showFrameRate)
        //    frame.setTitle(frametitle);   
    } else if (key == 'n') {
        projectnutrients = !projectnutrients;
        displayText("Project Nutrients:" + String.valueOf(projectnutrients));
    } else if (key == 'm') {
        mousestimdata = !mousestimdata;
        if (mousestimdata)
            displayText("Mouse mode set to data stimuli");
        else
            displayText("Mouse mode set to trail stimuli");
    } else if (key == 'c') {
        for (int y = 0; y < maxy; y++) {
            for (int x = 0; x < maxx; x++) {
                griddata[x][y] = 0;
            }
        }
        displayText("Clearing data field!");

    }
}



// allows writing of status messages at the bottom of the screen area
public void displayText(String st) {
    text(st, 10, hei - 10);
}


// manually specify the contents of the environment here, if not using a loaded image
public void createEnvironmentConfiguration() {
    // create background
    // original - grid.fillBackground(0);
    grid.fillBackground(51); // note that greyscale value RGB 51,51,51 is used to define a wall in the lattice!
    // create border
    grid.fillCircle(99, 99, 90, 0);
    // create obstacles



    // create data points for pg f6
    grid.setGridCellValue(73, 38, nodewid, 255);
    grid.setGridCellValue(105, 57, nodewid, 255);
    grid.setGridCellValue(157, 71, nodewid, 255);
    grid.setGridCellValue(46, 81, nodewid, 255);
    grid.setGridCellValue(91, 98, nodewid, 255);
    grid.setGridCellValue(45, 115, nodewid, 255);
    grid.setGridCellValue(118, 120, nodewid, 255);
    grid.setGridCellValue(152, 115, nodewid, 255);
    grid.setGridCellValue(98, 163, nodewid, 255);



    /*
   // create data points for pg f12
  grid.setGridCellValue(70,39,nodewid,255);
  grid.setGridCellValue(41,66,nodewid,255);  
  grid.setGridCellValue(91,65,nodewid,255);   
  grid.setGridCellValue(144,74,nodewid,255);   
  grid.setGridCellValue(47,105,nodewid,255);   
  grid.setGridCellValue(91,111,nodewid,255);   
  grid.setGridCellValue(135,112,nodewid,255);   
  grid.setGridCellValue(167,116,nodewid,255);     
  grid.setGridCellValue(56,143,nodewid,255);   
  grid.setGridCellValue(94,159,nodewid,255);   
  grid.setGridCellValue(139,155,nodewid,255);     
*/

    /*
       // create data points for pg f13
      grid.setGridCellValue(106,40,nodewid,255);
      grid.setGridCellValue(46,74,nodewid,255);  
      grid.setGridCellValue(83,95,nodewid,255);   
      grid.setGridCellValue(121,93,nodewid,255);   
      grid.setGridCellValue(53,131,nodewid,255);   
      grid.setGridCellValue(115,142,nodewid,255);   
      grid.setGridCellValue(158,134,nodewid,255);   
      grid.setGridCellValue(75,160,nodewid,255);     
    */

    // finally convert the grid data array into an image  
    convertGridArrayIntoImage();
}



public void convertGridArrayIntoImage() {
    bgimage = createImage(wid, hei, ALPHA);
    int count = 0;
    bgimage.loadPixels();
    int tv = 0;
    for (int y = 0; y < hei; y++) {
        for (int x = 0; x < wid; x++) {
            tv = grid.getGridCellValue(x, y);
            bgimage.pixels[count] = color(tv, tv, tv);
            count++;
        }
    }
    bgimage.updatePixels();
}




public void loadEnvironmentImage() {
    configImage = loadImage(imagestring);
    if (configImage == null) {
        System.out.println("Could not load image: " + imagestring);
        imageloaded = false;
        wid = 50;
        hei = 50;
    } else {
        wid = configImage.width;
        hei = configImage.height;
        imageloaded = true;
        System.out.println("Image: " + imagestring + ", loaded ok");
        System.out.println("width: " + wid + ",  height: " + hei);
    }
}



// respond to mouse clicks on the screen
public void mouseClicked() {
    if (mousestimdata) {
        grid.setGridCellValue(mouseX / 2, mouseY / 2, stimvalue);
    } else {
        grid.increaseTrail(mouseX / 2, mouseY / 2, stimvalue);
    }
}


// respond to mouse dragged events
public void mouseDragged() {
    if (mousestimdata) {
        grid.setGridCellValue(mouseX / 2, mouseY / 2, stimvalue);
    } else {
        grid.increaseTrail(mouseX / 2, mouseY / 2, stimvalue);
    }


}




// read and parse the text file to get node placement positions
public void readTextFile() {
    linecount = 0;
    String[] stuff = loadStrings(filename);
    if (stuff != null)
        fileloaded = true;
    System.out.println("File: " + filename + " Loaded: " + String.valueOf(fileloaded));
    // get number of samples from the first line
    data = (split(stuff[linecount], ','));
    numnodes = Integer.parseInt(data[1]);
    nodex = new float[numnodes];
    nodey = new float[numnodes];
    println("number of nodes found: " + numnodes);
    // parse node data
    linecount++; // move to the second line of the file - the start of the data 
    for (int t = 0; t < numnodes; t++) {
        data = split(stuff[linecount], ',');
        linecount++;
        nodex[t] = Float.parseFloat(data[0]);
        nodey[t] = Float.parseFloat(data[1]);
        println("Node: " + t + "\t\tx: " + nodex[t] + "\t\ty: " + nodey[t]);
    } // end t  
}




// draw the nodes on the screen
public void drawNodePositions() {
    stroke(255, 255, 255);
    int x = 0;
    int y = 0;
    for (int f = 0; f < numnodes; f++) {
        x = (int) nodex[f];
        y = (int) nodey[f];
        ellipse(x, y, 3, 3);
    }
}


// create lookup table of sin and cos values to improve speed
public void generateAngleLUTs() {
    sinlut = new double[SINCOS_LENGTH];
    coslut = new double[SINCOS_LENGTH];
    //  println("Angle lut lengths: "+SINCOS_LENGTH);
    for (int i = 0; i < SINCOS_LENGTH; i++) {
        sinlut[i] = (double) Math.sin(i * DEG_TO_RAD * SINCOS_PRECISION);
        coslut[i] = (double) Math.cos(i * DEG_TO_RAD * SINCOS_PRECISION);
        //   System.out.println(i+"  Sin: "+sinlut[i]+"      cos: "+ coslut[i]);
    }
}
public class Grid {
    // Grid is a structure to hold chemoattractant trails and particle IDs
    // The class also provides methods to diffuse trails, return trail levels to sensors, project data to nodes

    // initialises grid
    public Grid(int mx, int my) {
        maxx = mx;
        maxy = my;
        System.out.println("maxx: " + mx + ",  maxy: " + my);
        maxxminus = maxx - 1;
        maxyminus = maxy - 1;
        trail = new double[maxx][maxy];
        temptrail = new double[maxx][maxy];
        particle_ids = new int[maxx][maxy];
        griddata = new int[maxx][maxy];
        for (int y = 0; y < maxy; y++) {
            for (int x = 0; x < maxx; x++) {
                trail[x][y] = 0;
                temptrail[x][y] = 0;
                griddata[x][y] = 0;
                particle_ids[x][y] = -1;
            }
        }
    }


    // checks if a particle occupies this cell
    public boolean isOccupiedByParticle(int x, int y) {
        if (particle_ids[x][y] == -1)
            return false;
        else return true;
    }


    // puts a particle in this cell
    public void occupyGridCell(int x, int y, int id) {
        particle_ids[x][y] = id;
    }


    // remove a particle from this cell
    public void clearGridCell(int x, int y) {
        particle_ids[x][y] = -1;
    }


    // returns the trail value of a cell
    public double getTrailValue(int x, int y) {
        return trail[x][y];
    }


    // increase the trail value at a cell
    public void increaseTrail(int x, int y, double v) {
        trail[x][y] += v;
    }

    // return the data value from this cell
    public int getGridCellValue(int x, int y) {
        return griddata[x][y];
    }

    // set the data value of a cell
    public void setGridCellValue(int x, int y, int val) {
        griddata[x][y] = val; //issue mouse click
    }


    // set the value of a square field of cells
    public void setGridCellValue(int xpos, int ypos, int radius, int val) {
        if (radius < 1) {
            griddata[xpos][ypos] = val;
            return;
        }
        int sx = (int)(xpos - radius);
        int sy = (int)(ypos - radius);
        if (sx < 0)
            sx = 0;
        if (sy < 0)
            sy = 0;
        int endx = sx + (int)(radius * 2);
        int endy = sy + (int)(radius * 2);
        if (endx >= maxx)
            endx = maxx - 1;;
        if (endy >= maxy)
            endy = maxy - 1;
        for (int y = sy; y < endy; y++) {
            for (int x = sx; x < endx; x++) {
                griddata[x][y] = val;
            }
        }
    }



    // just check boundaries and wrap round, used by method which gets 3x3 trail window mean
    public double getTrailAndCheckBounds(int x, int y) {
        if (x < 0)
            x = maxxminus;
        if (x > maxxminus)
            x = 0;
        if (y < 0)
            y = maxyminus;
        if (y > maxyminus)
            y = 0;
        return getTrailValue(x, y);
    }



    // returns the mean of a 3x3 window of trails
    public double getAverageNeighbourhood(int x, int y) {
        double tot = 0;
        tot += getTrailAndCheckBounds(x - 1, y - 1);
        tot += getTrailAndCheckBounds(x, y - 1);
        tot += getTrailAndCheckBounds(x + 1, y - 1);
        tot += getTrailAndCheckBounds(x - 1, y);
        tot += getTrailAndCheckBounds(x, y);
        tot += getTrailAndCheckBounds(x + 1, y);
        tot += getTrailAndCheckBounds(x - 1, y + 1);
        tot += getTrailAndCheckBounds(x, y + 1);
        tot += getTrailAndCheckBounds(x + 1, y + 1);
        return tot / 9;
    }


    // diffuses the trail values, for both wraparound and non wrap conditions
    public void diffuseTrails() {
        if (wrap) // wrap - trail diffuses across toroidal boundary
        {
            double ave = 0;
            for (int y = 0; y < maxy; y++) {
                for (int x = 0; x < maxx; x++) {
                    ave = getAverageNeighbourhood(x, y);
                    temptrail[x][y] = ((1 - diffdamp) * ave); // stores in temp values
                }
            }
            for (int y = 0; y < maxy; y++) {
                for (int x = 0; x < maxx; x++) // updates real values from temp
                {
                    trail[x][y] = temptrail[x][y];
                    if (trail[x][y] < 0) trail[x][y] = 0;
                    if (griddata[x][y] == wallcol) trail[x][y] = 0; // remove trail from walled areas
                }
            }
        } else // non wrap condition - trail is absorbed at the border
        {
            double tot = 0;
            double ave = 0;
            for (int y = 0; y < maxy; y++) {
                for (int x = 0; x < maxx; x++) {
                    if (x < 1 || x >= maxxminus) // checks if exceeds bounds
                    {
                        temptrail[x][y] = 0;
                        continue;
                    }
                    if (y < 1 || y >= maxyminus) {
                        temptrail[x][y] = 0;
                        continue;
                    }
                    tot = 0;
                    tot += trail[x - 1][y - 1];
                    tot += trail[x][y - 1];
                    tot += trail[x + 1][y - 1];
                    tot += trail[x - 1][y];
                    tot += trail[x][y];
                    tot += trail[x + 1][y];
                    tot += trail[x - 1][y + 1];
                    tot += trail[x][y + 1];
                    tot += trail[x + 1][y + 1];
                    ave = tot / 9;
                    temptrail[x][y] = (1 - diffdamp) * ave; // stores in temp values
                }
            }
            for (int y = 0; y < maxy; y++) {
                for (int x = 0; x < maxx; x++) {
                    trail[x][y] = temptrail[x][y]; // updates temp vales
                    if (griddata[x][y] == wallcol) trail[x][y] = 0; // remove trail from walled areas            
                }
            }
        }
    }



    // slightly faster method of diffusion
    public void diffuseTrailsFast() {
        double tot = 0;
        double ave = 0;
        double damp = 1 - diffdamp;
        for (int y = 0; y < maxy; y++) {
            for (int x = 0; x < maxx; x++) {
                if (x < 1 || x >= maxxminus) // checks if exceeds bounds
                {
                    temptrail[x][y] = 0;
                    continue;
                }
                if (y < 1 || y >= maxyminus) {
                    temptrail[x][y] = 0;
                    continue;
                }
                if (griddata[x][y] == wallcol) {
                    continue;
                }
                tot = 0;
                tot += trail[x - 1][y - 1];
                tot += trail[x][y - 1];
                tot += trail[x + 1][y - 1];
                tot += trail[x - 1][y];
                tot += trail[x][y];
                tot += trail[x + 1][y];
                tot += trail[x - 1][y + 1];
                tot += trail[x][y + 1];
                tot += trail[x + 1][y + 1];
                ave = tot / 9;
                temptrail[x][y] = damp * ave; // stores in temp values
            }
        }
        for (int y = 0; y < maxy; y++) {
            for (int x = 0; x < maxx; x++) {
                trail[x][y] = temptrail[x][y]; // updates temp vales
                if (griddata[x][y] == wallcol) trail[x][y] = 0; // remove trail from walled areas            
            }
        }
    }



    // used to project data values at nodes (e.g. food locations) to trails
    public void projectToTrail() {
        // if we are using projection sites from a loaded image then scan through the image for projection values
        if (useLoadedImageForDataProjection && imageloaded) {
            for (int y = 0; y < maxy; y++) // are we using projection sites extracted from a loaded image?
            {
                for (int x = 0; x < maxx; x++) {
                    if (griddata[x][y] == projectcol)
                        increaseTrail(x, y, projectvalue);
                }
            }
        } else // or do we use the node positions loaded from the text file?
        {
            int x = 0;
            int y = 0;
            double pv = 0;
            for (int f = 0; f < numnodes; f++) {
                x = (int) nodex[f];
                y = (int) nodey[f];
                if (countNumberOfParticlesPresent(x, y) > 0) // if particles are on node, suppress the amount of chemoattractant deposited by the node
                    pv = suppressvalue;
                else
                    pv = projectvalue;
                increaseTrail(x - 1, y - 1, pv);
                increaseTrail(x, y - 1, pv);
                increaseTrail(x + 1, y - 1, pv);
                increaseTrail(x - 1, y, pv);
                increaseTrail(x, y, pv);
                increaseTrail(x + 1, y, pv);
                increaseTrail(x - 1, y + 1, pv);
                increaseTrail(x, y + 1, pv);
                increaseTrail(x + 1, y + 1, pv);
            }
        }
    }



    // returns how many, if any, particles are present in a particular neighbourhood
    public double countNumberOfParticlesPresent(int x, int y) {
        double count = 0;
        if (isOccupiedByParticle(x - 1, y - 1)) count++;
        if (isOccupiedByParticle(x, y - 1)) count++;
        if (isOccupiedByParticle(x + 1, y - 1)) count++;
        if (isOccupiedByParticle(x - 1, y)) count++;
        if (isOccupiedByParticle(x, y)) count++;
        if (isOccupiedByParticle(x + 1, y)) count++;
        if (isOccupiedByParticle(x - 1, y + 1)) count++;
        if (isOccupiedByParticle(x, y + 1)) count++;
        if (isOccupiedByParticle(x + 1, y + 1)) count++;
        return count;
    }



    // returns how many, if any, particles are present in a particular neighbourhood
    public double countNumberOfParticlesPresentWindow5(int x, int y) {
        double count = 0;
        for (int ty = -2; ty < 3; ty++) {
            for (int tx = -2; tx < 3; tx++) {
                if (isOccupiedByParticle(x + tx, y + ty)) count++;
            }
        }
        return count;
    }


    // returns how many, if any, particles are present in a particular neighbourhood set by the calling parameter
    public double countNumberOfVarWinParticlesPresent(int winsize, int x, int y) {
        int radius = winsize / 2;
        double count = 0;
        for (int ty = -radius; ty <= radius; ty++) {
            for (int tx = -radius; tx <= radius; tx++) {
                if (isOccupiedByParticle(x + tx, y + ty)) count++;
            }
        }
        return count;
    }



    // returns the maximum trail value, used in the method which rescales trail values for easy vision
    public double getMaxTrailValue() {
        double max = 0;
        for (int y = 1; y < maxyminus; y++) {
            for (int x = 1; x < maxxminus; x++) {
                if (trail[x][y] > max)
                    max = trail[x][y];
            }
        }
        return max;
    }



    // returns a trail value offset from the supplied position and orientation and distance
    public double getOffsetTrailValue(int x, int y, double angle, double offsetangle, double offsetsteps) {
        double tx = x;
        double ty = y;
        angle += offsetangle;
        if (angle > 360)
            angle -= 360;
        else if (angle < 0)
            angle += 360;
        if (useangleluts) {
            tx += coslut[(int) angle] * offsetsteps;
            ty += sinlut[(int) angle] * offsetsteps;
        } else {
            tx += Math.cos(getRadians(angle)) * offsetsteps;
            ty += Math.sin(getRadians(angle)) * offsetsteps;
        }
        tx = Math.round(tx);
        ty = Math.round(ty);
        if (wrap) // wrap condition - just return from other side of environment
        {
            if (ty < 0)
                ty = maxy - Math.abs(ty);
            else if (ty > maxyminus)
                ty = (ty - maxy);
            if (tx < 0)
                tx = maxx - Math.abs(tx);
            else if (tx > maxxminus)
                tx = (tx - maxx);
        } else // just some extra checks if non wrap is used - sends back '-1' if sensor is outside the environment
        {
            if (ty < 0)
                return outsidebordervalue;
            else if (ty >= maxy)
                return outsidebordervalue;
            if (tx < 0)
                return outsidebordervalue;
            else if (tx >= maxx)
                return outsidebordervalue;
        }
        return getTrailValue((int) tx, (int) ty);
    }


    // sets all cells to the values of the data supplied by a greyscale image
    public void setAllCellData(PImage img) {
        img.filter(GRAY);
        img.loadPixels();
        int count = 0;
        int c = 0;
        int r = 0;
        for (int y = 0; y < maxy; y++) {
            for (int x = 0; x < maxx; x++) {
                c = img.pixels[count]; // so we don't access the array too much
                r = (c & 0x00FF0000) >> 16; // red part only used because we must use 8 bit greyscale images to define the environment
                griddata[x][y] = r; // img.pixels[count] ;
                count++;
            }
        }
    }




    // fill all of the grid data with a certain value
    public void fillBackground(int val) {
        for (int y = 0; y < maxy; y++) {
            for (int x = 0; x < maxx; x++) {
                griddata[x][y] = val;
            }
        }
    }




    // fill a circle pattern to the grid of the specified position, radius and value
    public void fillCircle(int xpos, int ypos, int radius, int val) {
        if (radius == 1) // just check if it is not just a single point
        {
            griddata[xpos][ypos] = val;
            return;
        }
        int sx = (int)(xpos - radius);
        int sy = (int)(ypos - radius);
        if (sx < 0)
            sx = 0;
        if (sy < 0)
            sy = 0;
        int endx = sx + (int)(radius * 2);
        int endy = sy + (int)(radius * 2);
        if (endx >= maxx)
            endx = maxx - 1;;
        if (endy >= maxy)
            endy = maxy - 1;

        for (int y = sy; y < endy; y++) {
            for (int x = sx; x < endx; x++) {
                if (dist(x, y, xpos, ypos) <= radius)
                    griddata[x][y] = val;
            }
        }
    }


    // fill data in a rectangular shape, centred around the specified position and at the specified width, height and grey value
    public void fillIncreaseRectangularAreaCentredAroundValue(int xpos, int ypos, int width, int height, double value) {
        int widthhalf = width / 2;
        int heighthalf = height / 2;
        int sx = (int)(xpos - widthhalf);
        int sy = (int)(ypos - heighthalf);
        if (sx < 0)
            sx = 0;
        if (sy < 0)
            sy = 0;
        int endx = sx + width;
        int endy = sy + height;
        if (endx >= maxx)
            endx = maxxminus;;
        if (endy >= maxy)
            endy = maxyminus;
        for (int y = sy; y < endy; y++) {
            for (int x = sx; x < endx; x++) {
                increaseTrail(x, y, value);
            }
        }
    }




    // return the id tags of particles neighbouring this position (including the centre position, i.e. agent in the middle)
    public int[] getNeighbourhoodParticleIDs(int x, int y) {
        tempids[0] = particle_ids[x - 1][y - 1];
        tempids[1] = particle_ids[x][y - 1];
        tempids[2] = particle_ids[x + 1][y - 1];
        tempids[3] = particle_ids[x - 1][y];
        tempids[4] = particle_ids[x][y]; // current position
        tempids[5] = particle_ids[x + 1][y];
        tempids[6] = particle_ids[x - 1][y + 1];
        tempids[7] = particle_ids[x][y + 1];
        tempids[8] = particle_ids[x + 1][y + 1];
        return tempids;
    }

    // return the x,y location from a supplied surrounding neighbour index
    public Point getGridLocation(int index, int curx, int cury) {
        switch (index) {
            case 0:
                curx--;
                cury--;
                break;
            case 1:
                cury--;
                break;
            case 2:
                curx++;
                cury--;
                break;
            case 3:
                curx--;
                break;
            case 4:
                System.out.println("Error in grid get cell location - returned value of current cell ");
                break;
            case 5:
                curx++;
                break;
            case 6:
                cury++;
                curx--;
                break;
            case 7:
                cury++;
                break;
            case 8:
                curx++;
                cury++;
                break;
        }
        if (curx < 0)
            curx = maxxminus;
        if (curx > maxxminus)
            curx = 0;
        if (cury < 0)
            cury = maxyminus;
        if (cury > maxyminus)
            cury = 0;
        if (isOccupiedByParticle(curx, cury))
            return new Point(-1, -1);
        else
            return new Point(curx, cury);
    }



    // return the current position offset by a particular angle and radius
    public Point getPositionWhenSuppliedWithAngleAndRadius(int curx, int cury, double angleradians, double radius) {
        double tx = curx;
        double ty = cury;
        tx += Math.cos(angleradians) * radius;
        ty += Math.sin(angleradians) * radius;
        //  System.out.println("new angle: "+Misc.getDegrees(angleradians));
        tx = Math.round(tx);
        ty = Math.round(ty);
        if (ty < 0)
            ty = maxy - Math.abs(ty);
        else if (ty > maxyminus)
            ty = (ty - maxy);
        if (tx < 0)
            tx = maxx - Math.abs(tx);
        else if (tx > maxxminus)
            tx = (tx - maxx);
        return new Point((int) tx, (int) ty);
    }


} // end class Grid
public class Particle2d {

    // agent parameters
    int id = 0; // unique identifier
    double angle = 0; // orientation of agent in degrees
    int curx = 0; // current int x position
    int cury = 0; // current int y position
    int tempx = 0; // temporary x position
    int tempy = 0; // temporary y position
    double varx = 0; // double precision x position
    double vary = 0; // double precision y position
    double tempvarx = 0; // temporary double x position
    double tempvary = 0; // temporary double y position

    boolean moved_successfully = false; // has the agent moved forwards successfully in the attempt at movement?
    boolean divide = false;
    boolean die = false;
    Random r = new Random(); // to generate a uniformly distributed random value

    double fl, f, fr = 0; // store data from particle sensors




    public Particle2d() {}

    // each particle has unique id
    public Particle2d(int i) {
        id = i;
    }

    // place the particle at a random position and random orientation in the environment
    public void initialiseParticle() {
        do {
            tempx = getRand(maxxminus);
            tempy = getRand(maxyminus);
            //       tempx = (int)random((int)(startx-startradius), (int)(startx+startradius)); // start the particle at the position of the first mole in the list
            //      tempy = (int)random((int)(starty-startradius),(int)(starty+startradius));        
            //      } while (grid.isOccupiedByParticle(tempx,tempy));
        } while (!initSuccess(tempx, tempy));
        curx = tempx;
        cury = tempy;
        occupyCell(tempx, tempy);
        selectRandomDirection();
    }


    // place the particle at a random position and random orientation in the environment
    public void initialiseParticle(int x, int y) {
        tempx = x;
        tempy = y;
        curx = tempx;
        cury = tempy;
        occupyCell(tempx, tempy);
        selectRandomDirection();
    }



    // a number of tests to ensure correct initialisation
    public boolean initSuccess(int x, int y) {
        if (grid.isOccupiedByParticle(x, y)) // check if site is not already occupied
            return false;
        if (grid.getGridCellValue(x, y) == wallcol) // check if the site is not a wall
            return false;
        if (startcol != -1) // unless the agent can start on any colour (-1 tag) then check that the colour matches the desired start colour
        {
            if (grid.getGridCellValue(x, y) != startcol)
                return false;
        }
        return true;
    }


    // generates a random double between one and 'r' from a supplied int
    public double getDoubleRand(int r) {
        return (Math.random() * r) + 1;
    }


    // generates a random integer between one and 'r'
    public int getRand(int r) {
        return (int)(Math.random() * r) + 1;
    }




    // occupies a cell on the grid - clears old cell and occupies new cell
    // floating point positions reset to current integer position
    // chemoattractant trail is only deposited if agent moved forwards successfully
    //
    // this is not used often, only at initialisation of particle. Usually the instructions are hard coded into motor behaviour method
    //
    public void occupyCell(int tx, int ty) {
        grid.clearGridCell(curx, cury);
        grid.occupyGridCell(tempx, tempy, id);
        curx = tempx;
        cury = tempy;
        resetFloatingPointPosition();
        if (moved_successfully)
            grid.increaseTrail(curx, cury, depT);
    }



    // agent tries to move forwards
    public void doMotorBehaviours() {
        moved_successfully = false;
        // oscillation reset position test 
        if (osc && r.nextDouble() < oscresetprob) {
            resetFloatingPointPosition();
        }
        // randomly change direction?
        if (r.nextDouble() < pcd) // is a random turn being done?
        {
            selectRandomDirection();
            resetFloatingPointPosition();
            return;
        }
        if (useangleluts) {
            //   println(angle);  
            tempvarx += coslut[(int) angle] * speed;
            tempvary += sinlut[(int) angle] * speed;
        } else {
            tempvarx += Math.cos(getRadians(angle)) * speed;
            tempvary += Math.sin(getRadians(angle)) * speed;
        }
        if (wrap) // wrap condition
        {
            if (tempvarx > maxxminus)
                tempvarx -= maxx;
            if (tempvarx < 0)
                tempvarx = maxx + tempvarx;
            if (tempvary > maxyminus)
                tempvary -= maxy;
            if (tempvary < 0)
                tempvary = maxy + tempvary;
        } else // non wrap condition
        {
            if (tempvarx > maxxminus) {
                tempvarx = maxxminus - (tempvarx - maxx);
                angle = deg180 - angle;
            }
            if (tempvarx < 0) {
                tempvarx *= -1;
                angle = deg180 - angle;
            }
            if (tempvary > maxyminus) {
                tempvary = maxyminus - (tempvary - maxy);
                angle = deg360 - angle;
            }
            if (tempvary < 0) {
                tempvary *= -1;
                angle = deg360 - angle;
            }
        }
        varx = tempvarx;
        vary = tempvary;
        tempx = (int) Math.round(tempvarx);
        tempy = (int) Math.round(tempvary);

        if (tempx < 0)
            tempx = maxx + tempx;
        if (tempx > maxxminus)
            tempx -= maxx;
        if (tempy < 0)
            tempy = maxy + tempy;
        if (tempy > maxyminus)
            tempy -= maxy;
        if (grid.getGridCellValue(tempx, tempy) == wallcol) {
            resetFloatingPointPosition();
            selectRandomDirection();
            return;
        }
        if (grid.isOccupiedByParticle(tempx, tempy)) // just check new cell is not already occupied
        {
            if (osc) // if oscillatory behaviour switch is on, do not reset floating point position if particle cannot move
            {
                return;
            } else // no oscillatory behaviour, so reset floating point position to current cell and select new random direction to ensure fluid soap-film type flux
            {
                resetFloatingPointPosition();
                selectRandomDirection();
                return;
            }
        } else // cell is clear so: move into it and increase trail
        {
            moved_successfully = true;
            grid.clearGridCell(curx, cury);
            grid.occupyGridCell(tempx, tempy, id);
            curx = tempx;
            cury = tempy;
            grid.increaseTrail(curx, cury, depT);
            if (moved_successfully && !die && itercount % division_frequency_test == 0)
                // test for cell division - but only if we did not teleport to new cell and only if time and only if not marked to die
                doDivisionTest();

        }
    }


    // get a random direction
    public void selectRandomDirection() {
        angle = getDoubleRand(360);
        //  angle = getRadians(getDoubleRand(360));
    }



    // reset floating point values to current int grid position
    public void resetFloatingPointPosition() {
        varx = curx;
        vary = cury;
        tempvarx = curx;
        tempvary = cury;
    }


    // return position of particle, used in draw method
    public Point getPosition() {
        return new Point(curx, cury);
    }



    // get chemoattractant levels and rotate (but do not move) to face strongest
    public void doSensoryBehaviours() {
        if (adaptive_population_size && itercount % death_frequency_test == 0)
            doDeathTest();

        fl = grid.getOffsetTrailValue(curx, cury, angle, -sa, so); // return values to agent's sensors (front left, front, front right)
        f = grid.getOffsetTrailValue(curx, cury, angle, 0, so);
        fr = grid.getOffsetTrailValue(curx, cury, angle, sa, so);

        if ((!wrap) && (fl == -1 || fr == -1 || f == -1)) // check if non-wrap and sensors are outside boundary, prevents particles from 'sticking' at edges
        {
            rotate(ra);
            return;
        }

        if ((f > fl) && (f > fr)) // is front > both left and right?
        {
            return; // just continue facing in the same direction
        }
        if ((f < fl) && (f < fr)) // is front < both left and right?
        {
            if (fl < fr)
                rotate(ra);
            else rotate(-ra);
            return;
        }
        if (fl < fr) // is frontleft < frontright?
        {
            rotate(ra);
            return;
        }
        if (fr < fl) // is frontright < frontleft?
        {
            rotate(-ra);
        }
    }


    // rotates the particle by specified amount
    public void rotate(double r) {
        angle += r;
        if (angle < 0)
            angle += 360;
        else if (angle > 360)
            angle -= 360;
    }




    // test for cell division, if enabled
    public void doDivisionTest() {
        divide = false;
        if (isOutsideLatticeBorderRange(curx, cury))
            return;
        if (isWithinThresholdRange(curx, cury)) {
            if (r.nextDouble() < division_probability)
                divide = true;
        }
    }

    // test for death by overcrowding, if enabled
    public void doDeathTest() {
        die = false;
        if (isOutsideLatticeBorderRange(curx, cury))
            return;

        if (isOutsideSurvivalRange(curx, cury))
            die = true;
    }

    // used by division method
    public boolean isWithinThresholdRange(int x, int y) {
        double d = grid.countNumberOfVarWinParticlesPresent(gw, x, y);
        if (d > gmin && d <= gmax)
            return true;
        else return false;
    }

    // used by death test method
    public boolean isOutsideSurvivalRange(int x, int y) {

        double d = grid.countNumberOfVarWinParticlesPresent(sw, x, y);
        if (d < smin || d > smax)
            return true;
        else return false;
    }


    public boolean isOutsideLatticeBorderRange(int x, int y) {
        boolean value = false;
        if (x < divisionborder || x > (wid - divisionborder))
            return true;
        else if (y < divisionborder || y > (hei - divisionborder))
            return true;
        else return false;
    }


} // end class Particle2d
public class Point
{
  
  public int x ;
  public int y ;
  
  public Point()
  {
    x = 0 ;
    y = 0 ;
  }
  
  public Point(int px, int py)
  {
    x = px ;
    y = py ;
  }
  
  
}
  public void settings() {  size(876, 876); }
  static public void main(String[] passedArgs) {
    String[] appletArgs = new String[] { "--present", "--window-color=#666666", "--stop-color=#cccccc", "PhysarumVeinsMark1" };
    if (passedArgs != null) {
      PApplet.main(concat(appletArgs, passedArgs));
    } else {
      PApplet.main(appletArgs);
    }
  }
}
