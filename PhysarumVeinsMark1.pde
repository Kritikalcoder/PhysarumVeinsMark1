import java.util.ArrayList;
import java.util.Random;
import java.util.*;
import processing.sound.*;
import processing.video.*;

int popsize = 10000; // initial particle population size
int pixienum = popsize; // the current number of agent particles
double so = 15; // sensor offset distance (a scaling parameter)

double sa = 30; // sensor angle in degrees from forward position

double ra = 20; // rotation angle in degrees (how much the particle should turn)

boolean osc = false; // is oscillatory (flux resistant) movement activated?     *****  this would not be relevant for CA implementation
double pcd = 0; // probability of a random change in direction
double oscresetprob = 0.01; // probability of resetting oscillation counter (if in oscillatory mode)
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
double diffdamp = 0.1; // diffusion damping value. Damping is 1-diffdamp so if diffdamp is 0.1 then the diffused value would be (value)*0.9
double projectvalue = 200; // how big is the value for the data nodes which we project onto the chemoattractant field
double suppressvalue = 2.5; // projection value if blob is covered by particles
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
final double deg180 = 3.14159265358979;
final double deg360 = 6.28318531;
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
float changevalue = 2.5; // how much do we change angles by when the user presses change keys
int stimvalue = 255; // how big is the value by which mouse stimulation is given?
String frametitle = "";
PImage pixelimage; // stores offscreen buffer of main image

PImage imagery;

WhiteNoise noise;
Capture cam;
void setup() {


    generateAngleLUTs(); // generate look-up table for faster angle calculations
    createEnvironment();
    popsize = pixienum;
    // general initialisation    
    size(876, 876);
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
    noise.amp(0.01);

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


void draw() {
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
        frame.setTitle(int(frameRate) + " fps");

    noise.pan(map(mouseX, 0, width, -1.0, 1.0));
    noise.amp(map(mouseX + mouseY, 0, width + height, 0, 0.05));
    saveFrame("screen-####.png");
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
void keyPressed() {
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
        oscresetprob -= 0.01;
        if (oscresetprob < 0)
            oscresetprob = 0;
        displayText("pOscReset: " + oscresetprob);
    } else if (key == '8') // increase prob of osc reset
    {
        oscresetprob += 0.01;
        if (oscresetprob > 1)
            oscresetprob = 1;
        displayText("pOscReset: " + oscresetprob);
    }

    if (key == '9') // decrease prob of change direction
    {
        pcd -= 0.01;
        if (pcd < 0)
            pcd = 0;
        displayText("pChangeDir: " + pcd);
    } else if (key == '0') // increase prob of change direction
    {
        pcd += 0.01;
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
void displayText(String st) {
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
void mouseClicked() {
    if (mousestimdata) {
        grid.setGridCellValue(mouseX / 2, mouseY / 2, stimvalue);
    } else {
        grid.increaseTrail(mouseX / 2, mouseY / 2, stimvalue);
    }
}


// respond to mouse dragged events
void mouseDragged() {
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