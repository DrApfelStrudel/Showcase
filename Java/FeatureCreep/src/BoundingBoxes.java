import java.util.ArrayList;

public class BoundingBoxes {
	private ArrayList<BoundingBox> boxes;
	
	public BoundingBoxes() {
		boxes = new ArrayList<BoundingBox>();
	}
	
	public void addBox(BoundingBox bb) {
		boxes.add(bb);
	}
	
	public boolean collide(BoundingBox bb) {
		for (BoundingBox b : boxes) {
			if (b.collide(bb)) {
				return true;
			}
		}
		return false;
	}
	
	public boolean collide(BoundingBoxes bb) {
		for (BoundingBox b : boxes) {
			for (BoundingBox c : bb.boxes) {
				if (b.collide(c)) {
					return true;
				}
			}
		}
		return false;
	}
}
