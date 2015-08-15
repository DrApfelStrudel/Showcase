import java.util.ArrayList;


public class Tile {
	public int x,y,z;
	private ArrayList<Tile> n;
	private Tile parent = null;
	private BoundingBox bb;
	public Point color = new Point(1f,1f,1f);
	public boolean jumpTile = false;
	
	public Tile(int x, int y, int z) {
		this.x = x;
		this.y = y;
		this.z = z;
		n = new ArrayList<Tile>();
		Point po = Util.toPos(new Point(x,y,z));
		bb = new BoundingBox(po.x,po.y+0.25f,po.z,0.5f,0.5f,0.5f);
	}
	
	public ArrayList<Tile> nb() {
		return n;
	}
	
	public Tile getParent() {
		return parent;
	}
	
	public void setParent(Tile t) {
		parent = t;
	}
	
	public void addNeighbour(Tile t) {
		n.add(t);
		t.n.add(this);
	}
	
	public void draw() {
		Point po = Util.toPos(new Point(x,y,z));
		new Cube3D(po.x+0.125f, po.y, po.z+0.125f, 0.25f, 0.25f, 0.25f, color, TexLoad.tex[5]).draw();
		for (Tile e : n) {
			float la = (Util.toPos(e.getPos()).x - Util.toPos(getPos()).x);
			float ha = (Util.toPos(e.getPos()).y - Util.toPos(getPos()).y);
			float ba = (Util.toPos(e.getPos()).z - Util.toPos(getPos()).z);
			float xa = la/2 + Util.toPos(getPos()).x;
			float ya = ha/2 + Util.toPos(getPos()).y;
			float za = ba/2 + Util.toPos(getPos()).z;
			Cube3D check = new Cube3D(xa,ya,za,Math.abs(la)+0.125f,Math.abs(ha)+0.125f,Math.abs(ba)+0.125f, new Point(0f,1f,0f), TexLoad.tex[3]); 
			check.update();
			check.draw();
		}
	}
	
	public boolean canSee(Entity e) {
		float la = (e.getPos().x - Util.toPos(getPos()).x);
		float ha = (e.getPos().y - Util.toPos(getPos()).y);
		float ba = (e.getPos().z - Util.toPos(getPos()).z);
		float xa = la/2 + Util.toPos(getPos()).x;
		float ya = ha/2 + Util.toPos(getPos()).y;
		float za = ba/2 + Util.toPos(getPos()).z;
		Cube3D check = new Cube3D(xa,ya,za,Math.abs(la),Math.abs(ha),Math.abs(ba), new Point(0f,1f,0f), TexLoad.tex[1]); 
		check.update();
		for (Cube3D cu : Data.cubes) {
			if (cu.bounds.collide(check.bounds)) {
				if(cu.getCoords().y-Util.toPos(getPos()).y >= 0.2f)
				return false;
			}
		}
		return Util.distanceFrom(Util.toPos(getPos()), e.getPos()) < 50;
	}
	
	public void upY(int y) {
		this.y += y;
	}
	
	public String toString() {
		return "[" + x + ", " + y + ", " + z + "]";
	}
	
	public boolean equals(Object o) {
		Tile t = (Tile) o;
		return x == t.x && z == t.z;
	}
	
	public Point getPos() {
		return new Point(x,y,z);
	}
	
	public boolean TileCollide() {
		for (Cube3D c : Data.cubes) {
			if (bb.collide(c.bounds)) {
				return true;
			}
		}
		return false;
	}
}
