
import java.awt.event.ActionListener;

/*
 * Click nbfs://nbhost/SystemFileSystem/Templates/Licenses/license-default.txt to change this license
 * Click nbfs://nbhost/SystemFileSystem/Templates/Classes/Interface.java to edit this template
 */

/**
 *
 * @author cirom
 */
public interface DataByFrame {
    public void addActionListener(ActionListener listener);
    public void removeActionListener(ActionListener listener);
    public Tableaux getTableauxReference();
}
