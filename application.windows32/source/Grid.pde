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