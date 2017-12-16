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